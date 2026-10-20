module

public import ComparisonActualHighWallBareGaContrastKernel
public import ComparisonActualHighWallResourceGaCurrentAlong
public import ComparisonActualHighWallResourceGRestorationFromMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
open NativeOverlapMinimum
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualHighWallBareGaOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree rBound : ℕ) (eta Cmass Ccut p C : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(U : ℕ) (seed : List NativeResourceMark)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term →
      st.term.resources.length ≤ degree → 0 < mid.length → pre.length+mid.length < U →
      U ≤ (pre++(mid++tail)).length → st.tree.leaves ≤ rBound →
    ∀x V : ℝ,(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → W n ≤ V → V ≤ 1 →
      V ≤ (M n).data.wallRadius (M n).alpha (partitionPoint 0 as U) →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      partitionPoint 0 as U ≤ Ccut*(M n).data.d →
    let R:=(M n).data.highErrorEnvelope (M n).alpha (pre++(mid++tail)) U
    |((W n)⁻¹)^st.generation*actualGeneralFourGaContrast (M n).bf (M n).hf U st| ≤ 
      |st.term.coefficient| *nativeResourceScale x (W n) 1 seed*C*
        (((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)+(M n).data.d*
          (st.tree.forkCost (fun l=>(R l)^(4/p))+edgeBudget 0 (pre++(mid++tail)) (fun l=>(R l)^(4/p))+
            (M n).data.d*(st.tree.forkCost R+edgeBudget 0 (pre++(mid++tail)) R)))

theorem actual_high_wall_same_star_bare_Ga_along
    (hdim : Tendsto dim atTop atTop)
    {m delta eta saving cl cu Az C0 Ct D Bclock : ℝ}
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Cmass Ccut : ℝ) (hCm : 1 ≤ Cmass) (hCcut : 0 ≤ Ccut) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0)) (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃C : ℝ,0 < C ∧ ActualHighWallBareGaOnEveryFinalNetAlong degree rBound eta Cmass Ccut p C M W w := by
  obtain ⟨Cc,hCc,HC⟩:=actual_high_wall_same_star_resource_Ga_current_along hdim degree (rBound+1)
    Cmass hCm heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hfixed hsaving w Hmixed
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_resource_G_restoration_from_minimum
    (D:=D) degree dOrder (rBound+1) hd p hp hOrder Bclock Cmass Ccut (zero_le_one.trans hCm) hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Bc:=max Bclock 0
  let C:=Bc*Cc+2*Bc*Cr+1
  have hBc : 0 ≤ Bc:=le_max_right _ _
  have hC : 0 < C:=by dsimp only [C];positivity
  have hCcPrice : Bc*Cc ≤ C:=by
    have H:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hBc) hCr.le
    dsimp only [C]
    linarith only [H]
  have hCrPrice : 2*Bc*Cr ≤ C:=by
    have H:=mul_nonneg hBc hCc.le
    dsimp only [C]
    linarith only [H]
  refine ⟨C,hC,?_⟩
  filter_upwards [HC,hdim.eventually HR] with n hnC hnR
  intro L us hus hret hmesh hstar
  filter_upwards [hnC L us hus hret hmesh hstar,hnR (M n) (hfixed n) L us hus hret hmesh] with j hjC hjR
  dsimp only at hjC hjR ⊢
  intro pre mid tail hcut hindex hmass U seed st hP hdegree hmid hs hU hT
    x V hx hxW hmi hWV hV1 hVU hlow hz hcutmass
  let as:=pre++(mid++tail)
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target (pre.length+mid.length)
  have hi : pre.length ≤ pre.length+mid.length:=by omega
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    exact hcut.symm ▸ finiteCutMasses_ordered us hus j
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target _)
    omega
  have Hc0:=hjC pre mid tail hcut hindex hmass st.tree U st.generation seed st.term hP hdegree hmid hs hU
    (by omega) x V hx hxW hmi hWV hV1 hVU hlow hz
  have Hc1:=hjC pre mid tail hcut hindex hmass g.tree U st.generation seed (st.term.retarget 0) hP.retarget
    (by simpa only [NativeResourceTerm.retarget_resources] using hdegree) hmid hs hU hg
    x V hx hxW hmi hWV hV1 hVU hlow hz
  have hxEq : x=(M n).data.d:=le_antisymm (hxW.trans_eq (hcanonical n)) (by simpa only [hfixed n] using hx)
  have hdepth : seed.length+st.generation ≤ degree:=by rw [←hP.total_factor_depth];exact hdegree
  rw [←hcut] at hjR
  have hmi' : partitionPoint 0 as pre.length ≤ Cmass*(M n).data.d:=by simpa only [as,hcut,hxEq] using hmi
  have hms' : partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*(M n).data.d:=by simpa only [as,hcut,hcanonical n] using hmass
  have hcut' : partitionPoint 0 as U ≤ Ccut*(M n).data.d:=by simpa only [as,hcut] using hcutmass
  have Hr0:=hjR pre.length (pre.length+mid.length) U st.generation seed st.tree st.term hP hi hs hU
    (by omega) hdepth hmi' hms' hcut'
  have Hr1:=hjR pre.length (pre.length+mid.length) U st.generation seed g.tree (st.term.retarget 0)
    hP.retarget hi hs hU hg hdepth hmi' hms' hcut'
  let R:=(M n).data.highErrorEnvelope (M n).alpha as U
  let profile:=st.tree.forkCost (fun l=>(R l)^(4/p))+edgeBudget 0 as (fun l=>(R l)^(4/p))+
    (M n).data.d*(st.tree.forkCost R+edgeBudget 0 as R)
  have hlo l (hl : l < U) : R l=0:=by
    simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hl,ite_true]
  have hfl l (hl : l < U) : (R l)^(4/p)=0:=by
    rw [hlo l hl,Real.zero_rpow (ne_of_gt (div_pos (by norm_num) (by linarith : 0 < p)))]
  have Hfork:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs R hlo
  have Hforkf:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs (fun l=>(R l)^(4/p)) hfl
  change g.tree.forkCost R=st.tree.forkCost R at Hfork
  change g.tree.forkCost (fun l=>(R l)^(4/p))=st.tree.forkCost (fun l=>(R l)^(4/p)) at Hforkf
  have hR l : 0 ≤ R l:=(M n).data.highErrorEnvelope_nonneg (M n).alpha as U l
  have hprofile : 0 ≤ profile:=by
    dsimp only [profile]
    exact add_nonneg (add_nonneg (st.tree.forkCost_nonneg (fun l=>Real.rpow_nonneg (hR l) _))
      (edgeBudget_nonneg ho (fun l=>Real.rpow_nonneg (hR l) _)))
      (mul_nonneg (M n).data.hd.le (add_nonneg (st.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  let scale:=|st.term.coefficient| *nativeResourceScale x (W n) 1 seed
  let rate:=((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)
  let A:=scale*Cc*rate
  let B:=scale*Cr*(M n).data.d*profile
  have hW : 0 < W n:=by rw [hcanonical n];exact (M n).data.hd
  have hx0 : 0 < x:=(M n).hxs.trans_le hx
  have hscale : 0 ≤ scale:=mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed hx0 hW).le
  have hrate : 0 ≤ rate:=by dsimp only [rate];positivity
  have hA : 0 ≤ A:=by dsimp only [A];positivity
  have hB : 0 ≤ B:=by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg hscale hCr.le) (M n).data.hd.le) hprofile
  have Hc0' : |((W n)⁻¹)^st.generation*actualGeneralResourceGaCurrent (M n).bf (M n).hf U st.term| ≤ A:=by
    convert Hc0 using 1
    dsimp only [A,rate,scale]
    ring
  have Hc1' : |((W n)⁻¹)^st.generation*actualGeneralResourceGaCurrent (M n).bf (M n).hf U (st.term.retarget 0)| ≤ A:=by
    convert Hc1 using 1
    dsimp only [A,rate,scale,NativeResourceTerm.retarget]
    ring
  have Hr0' : |((W n)⁻¹)^st.generation*actualGeneralResourceGaRestoration (M n).bf (M n).hf U st.term| ≤ B:=by
    convert Hr0 using 1
    all_goals first | dsimp only [B,scale,profile,R,as] | skip
    all_goals rw [hcanonical n]
    all_goals rw [hxEq]
    all_goals ring_nf
  have Hr1' : |((W n)⁻¹)^st.generation*actualGeneralResourceGaRestoration (M n).bf (M n).hf U (st.term.retarget 0)| ≤ B:=by
    change |((M n).data.d⁻¹)^st.generation*actualGeneralResourceGaRestoration (M n).bf (M n).hf U (st.term.retarget 0)| ≤ 
      |st.term.coefficient| *nativeResourceScale (M n).data.d (M n).data.d 1 seed*
        (Cr*(M n).data.d*(g.tree.forkCost (fun l=>(R l)^(4/p))+edgeBudget 0 as (fun l=>(R l)^(4/p))+
          (M n).data.d*(g.tree.forkCost R+edgeBudget 0 as R))) at Hr1
    rw [Hforkf,Hfork] at Hr1
    convert Hr1 using 1
    all_goals first | dsimp only [B,scale,profile,R,as] | skip
    all_goals rw [hcanonical n]
    all_goals rw [hxEq]
    all_goals ring_nf
  have H:=actual_high_wall_bare_Ga_contrast_bound (M n) st hP hi hs ho hU (W n) A B hA hB Hc0' Hc1' Hr0' Hr1'
  apply H.trans
  change Bc*(A+2*B) ≤ _
  calc
    Bc*(A+2*B)=scale*((Bc*Cc)*rate+(2*Bc*Cr)*((M n).data.d*profile)):=by dsimp only [A,B];ring
    _ ≤ scale*(C*rate+C*((M n).data.d*profile)):=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hCcPrice hrate)
        (mul_le_mul_of_nonneg_right hCrPrice (mul_nonneg (M n).data.hd.le hprofile))) hscale
    _= _:=by dsimp only [scale,rate,profile,R,as];ring

end OAI.SKFluctuations.Cavity
