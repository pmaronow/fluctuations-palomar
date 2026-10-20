module

public import ComparisonActualHighWallResourceRetainedGammaAlong
public import ComparisonActualGeneralFourRetainedGammaRawPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
variable {dim : ℕ→ℕ}

def ActualHighWallFourRetainedGammaRawOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree rBound : ℕ) (eta Cmass C : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→(w n).star∈us→
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as→
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as→
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n→
    ∀(U : ℕ) (seed : List NativeResourceMark)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term→
      st.term.resources.length ≤ degree→0 < mid.length→pre.length+mid.length < U→
      U ≤ (pre++(mid++tail)).length→st.tree.leaves ≤ rBound→
    ∀x V : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as pre.length ≤ Cmass*x→
      W n ≤ V→V ≤ 1→V ≤ (M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)→
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2→(M n).z ≤ V/2→
      |(W n)⁻¹^st.generation*actualGeneralFourCategoryContrast (M n).bf (M n).hf U st .gammaRetained| ≤ 
        |st.term.coefficient| *C*(dim n:ℝ)^(-eta)*(W n*(M n).xs^2)*nativeResourceScale x (W n) 1 seed

theorem actual_high_wall_four_retained_Gamma_raw_from_resource_rows_along
    {m delta cl cu Az C0 Ct D Bclock eta Cmass C₀ : ℝ}
    (degree rBound : ℕ) (hC₀ : 0 < C₀)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (HX : ∀n,(M n).xs ≤ W n)
    (Hrows : ActualHighWallResourceRetainedGammaOnEveryFinalNetAlong degree (rBound+1) eta Cmass C₀ M W w) :
    ∃C : ℝ,0 < C ∧ ActualHighWallFourRetainedGammaRawOnEveryFinalNetAlong degree rBound eta Cmass C M W w := by
  let Bclock0:=max Bclock 0
  let C:=1+Bclock0*C₀
  have hB : 0 ≤ Bclock0:=le_max_right _ _
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [Hrows] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  intro pre mid tail hcut hindex hmass U seed st hP hdegree hmid hs hU hleaves x V hx hxW hmi hWV hV1 hVU hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus j
  have hi : pre.length ≤ pre.length+mid.length:=by omega
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target (pre.length+mid.length)
  have hg : g.tree.leaves ≤ rBound+1:=
    (st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target (pre.length+mid.length))).trans
      (Nat.add_le_add_right hleaves 1)
  have H0:=hj pre mid tail hcut hindex hmass st.tree U st.generation seed st.term hP hdegree
    hmid hs hU (by omega) x V hx hxW hmi hWV hV1 hVU hlow hz
  have H1:=hj pre mid tail hcut hindex hmass g.tree U st.generation seed (st.term.retarget 0)
    hP.retarget (by simpa only [NativeResourceTerm.retarget_resources] using hdegree)
    hmid hs hU hg x V hx hxW hmi hWV hV1 hVU hlow hz
  let B:=C₀*(dim n:ℝ)^(-eta)*(W n*(M n).xs^2)*nativeResourceScale x (W n) 1 seed
  have hW : 0 < W n:=(M n).hxs.trans_le (HX n)
  have hx0 : 0 < x:=(M n).hxs.trans_le hx
  have hseed : 0 ≤ nativeResourceScale x (W n) 1 seed:=(actual_resource_raw_scale_pos seed hx0 hW).le
  have hBB : 0 ≤ B:=by simp only [B];positivity
  have hBond : ((M n).bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ) ≤ Bclock0:=by
    have HT:=(M n).data.total_clock_le (M n).alpha (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))
      (partitionPoint_mem (pre++(mid++tail)) ho (pre.length+mid.length))
    have Hh:=(M n).hf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)) |>.coe_nonneg
    exact (show ((M n).bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ) ≤ (M n).data.T by linarith).trans
      ((M n).hT.trans (le_max_left _ _))
  have H:=actual_general_four_retained_gamma_raw_abs_le (M n).bf (M n).hf
    ((M n).data.wallRadius (M n).alpha) ((M n).data.wallRadius_monotone (M n).alpha)
    ((M n).data.bf_monotone (M n).alpha) ((M n).data.hf_monotone (M n).alpha)
    st hP hi hs ho V (by simpa only [hcut] using hVU) hBB hB hBond
    (by convert H0 using 1; dsimp only [B]; ring)
    (by convert H1 using 1; dsimp only [B,NativeResourceTerm.retarget]; ring)
  apply H.trans
  have HC : Bclock0*C₀ ≤ C:=by dsimp only [C];linarith
  have HH:=mul_le_mul_of_nonneg_left HC
    (show 0 ≤ |st.term.coefficient| *(dim n:ℝ)^(-eta)*(W n*(M n).xs^2)*nativeResourceScale x (W n) 1 seed by positivity)
  convert HH using 1 <;> (try dsimp only [B]) <;> ring

end OAI.SKFluctuations.Cavity
