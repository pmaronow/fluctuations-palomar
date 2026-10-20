module

public import ComparisonSignedCavityOriginalGWordSquaredBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

def nativeActualProfileOpVariation (r : ℕ) : NativeActualExpansionOp→ℝ
  | .center=>2
  | .reweight c=>|c|
  | .retarget=>1
  | .projection=>1
  | .highRow=>4*(r:ℝ)+1

def nativeActualProfileVariation : ℕ→List NativeActualExpansionOp→ℝ
  | _,[]=>1
  | r,op::ops=>nativeActualProfileOpVariation r op*nativeActualProfileVariation (r+2) ops

theorem nativeActualProfileVariation_nonneg (r : ℕ) (ops : List NativeActualExpansionOp) :
    0≤nativeActualProfileVariation r ops := by
  induction ops generalizing r with
  | nil=>exact zero_le_one
  | cons op ops ih=>
    apply mul_nonneg _ (ih _)
    cases op <;> simp [nativeActualProfileOpVariation] <;> positivity

theorem nativeActualHighProfileResourceStep_leaves_le
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star<U) (hl : star≤as.length) (op : NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) (r : ℕ) (hr : st.tree.leaves≤r)
    (Q : NativeActualResourceState S as i star) (hQ : Q∈nativeActualResourceStep Γ hs hl op st) :
    Q.tree.leaves≤r+2 := by
  have HF : (nativeFreshAtSlot st.tree 0 st.term.live.test.target star).tree.leaves≤r+1 := by
    exact (st.tree.markedAttach_leaves 0 _ (nativeFreshAtSlot_mem _ _ _ _)).trans (by omega)
  cases op with
  | center=>
    simp only [nativeActualResourceStep,List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with hQ|hQ
    · rw [hQ]
      exact hr.trans (by omega)
    · rw [hQ]
      change st.tree.leaves≤r+2
      omega
  | reweight c=>
    simp only [nativeActualResourceStep,List.mem_cons,List.not_mem_nil,or_false] at hQ
    subst Q
    exact hr.trans (by omega)
  | retarget=>
    simp only [nativeActualResourceStep,List.mem_cons,List.not_mem_nil,or_false] at hQ
    subst Q
    exact HF.trans (by omega)
  | projection=>
    simp only [nativeActualResourceStep,List.mem_cons,List.not_mem_nil,or_false] at hQ
    subst Q
    exact HF.trans (by omega)
  | highRow=>
    simp only [nativeActualResourceStep] at hQ
    obtain ⟨p,hp,hQ⟩:=List.mem_flatMap.mp hQ
    split_ifs at hQ with hh
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
      subst Q
      have H1:=st.tree.markedAttach_leaves 0 p.val p.property
      have H2:=p.val.tree.markedAttach_leaves 0 _
        (nativeFreshAtSlot_mem p.val.tree 0 (p.val.embed st.term.live.test.target) star)
      change (nativeFreshAtSlot p.val.tree 0 (p.val.embed st.term.live.test.target) star).tree.leaves≤r+2
      omega
    · exact False.elim (List.not_mem_nil hQ)

theorem nativeActualResourceStep_wholeProfile_le (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (op : NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) (r : ℕ) (hr : st.tree.leaves≤r)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((nativeActualResourceStep Γ hs hl op st).map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
      |st.term.coefficient| *nativeActualProfileOpVariation r op*(st.tree.forkCost f+edgeBudget 0 as f) := by
  have HB:=edgeBudget_nonneg ho hf
  have HT:=st.tree.forkCost_nonneg hf
  have HF:=nativeFreshAtSlot_high_forkCost st.tree 0 st.term.live.test.target hs f hlo
  cases op with
  | center=>
    simp only [nativeActualResourceStep,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,NativeActualResourceState.freeze,NativeResourceTerm.freeze,abs_neg,nativeActualProfileOpVariation]
    ring_nf
    exact le_refl _
  | reweight c=>
    simp only [nativeActualResourceStep,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,NativeActualResourceState.reweight,NativeResourceTerm.reweight,abs_mul,nativeActualProfileOpVariation]
    ring_nf
    exact le_refl _
  | retarget=>
    simp only [nativeActualResourceStep,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,NativeActualResourceState.retarget,NativeResourceTerm.retarget,nativeActualProfileOpVariation,mul_one,HF]
    exact le_refl _
  | projection=>
    simp only [nativeActualResourceStep,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,NativeActualResourceState.projection,NativeResourceTerm.projection,nativeActualProfileOpVariation,mul_one,HF]
    exact le_refl _
  | highRow=>
    have HC : 0≤|st.term.coefficient|:=abs_nonneg _
    have HR (p : MarkedPlacement st.tree) (hp : p∈st.tree.markedAttach 0) :
        |p.coeff| *|Γ st.toHigh p| *(p.tree.forkCost f+edgeBudget 0 as f) ≤
        |p.coeff| *(p.tree.forkCost f+edgeBudget 0 as f) := by
      have H:=mul_le_of_le_one_left
        (add_nonneg (p.tree.forkCost_nonneg hf) HB) (hΓ st.toHigh p hp)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H (abs_nonneg p.coeff)
    have Hsum : ((nativeActualResourceStep Γ hs hl .highRow st).map (fun Q=>|Q.term.coefficient| *
        (Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
        |st.term.coefficient| *((st.tree.markedAttach 0).map
          (fun p=>|p.coeff| *(p.tree.forkCost f+edgeBudget 0 as f))).sum := by
      unfold nativeActualResourceStep
      simp only [List.map_flatMap,native_sum_flatMap]
      conv_rhs => rw [←List.sum_map_mul_left,←List.attach_map_val]
      apply List.sum_le_sum
      intro p hp
      split_ifs with hh
      · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
        rw [NativeActualResourceState.markedRow_coefficient]
        have HG:=nativeFreshAtSlot_high_forkCost p.val.tree 0 (p.val.embed st.term.live.test.target) hs f hlo
        change |p.val.coeff*Γ st.toHigh p.val*st.term.coefficient| *
          ((nativeFreshAtSlot p.val.tree 0 (p.val.embed st.term.live.test.target) star).tree.forkCost f+_)≤_
        rw [HG,abs_mul,abs_mul]
        have H:=mul_le_mul_of_nonneg_left (HR p.val p.property) HC
        nlinarith only [H]
      · simp only [List.map_nil,List.sum_nil]
        exact mul_nonneg HC (mul_nonneg (abs_nonneg _) (add_nonneg (p.val.tree.forkCost_nonneg hf) HB))
    have HH:=st.tree.markedAttach_forkCost_le ho hf
    have HV:=st.tree.markedAttach_variation ho
    have Hcast : (st.tree.leaves:ℝ)≤r:=by exact_mod_cast hr
    have Hrows : ((st.tree.markedAttach 0).map
        (fun p=>|p.coeff| *(p.tree.forkCost f+edgeBudget 0 as f))).sum≤
        (4*(r:ℝ)+1)*(st.tree.forkCost f+edgeBudget 0 as f) := by
      simp only [mul_add,List.sum_map_add,List.sum_map_mul_right,HV,sub_zero]
      have Hx:=mul_nonneg (sub_nonneg.mpr Hcast) (add_nonneg HT HB)
      nlinarith
    exact Hsum.trans (by
      simpa only [nativeActualProfileOpVariation,mul_assoc] using mul_le_mul_of_nonneg_left Hrows HC)

theorem nativeActualResourceExpansion_wholeProfile_le (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (ops : List NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) (r : ℕ) (hr : st.tree.leaves≤r)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((nativeActualResourceExpansion Γ hs hl ops st).map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
      |st.term.coefficient| *nativeActualProfileVariation r ops*(st.tree.forkCost f+edgeBudget 0 as f) := by
  induction ops generalizing st r with
  | nil=>simp only [nativeActualResourceExpansion,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,nativeActualProfileVariation,mul_one,le_refl]
  | cons op ops ih=>
    let C:=nativeActualProfileVariation (r+2) ops
    have HC : 0≤C:=nativeActualProfileVariation_nonneg _ _
    have HI : ((nativeActualResourceExpansion Γ hs hl (op::ops) st).map
        (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
        C*((nativeActualResourceStep Γ hs hl op st).map
          (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum := by
      simp only [nativeActualResourceExpansion,List.map_flatMap,native_sum_flatMap]
      rw [←List.sum_map_mul_left]
      apply List.sum_le_sum
      intro Q hQ
      have HQ:=nativeActualHighProfileResourceStep_leaves_le Γ hs hl op st r hr Q hQ
      have H:=ih Q (r+2) HQ
      simpa only [C,mul_assoc,mul_left_comm,mul_comm] using H
    have HS:=nativeActualResourceStep_wholeProfile_le ho Γ hΓ hs hl op st r hr f hf hlo
    apply HI.trans
    have H:=mul_le_mul_of_nonneg_left HS HC
    convert H using 1 <;> simp only [nativeActualProfileVariation,C] <;> ring

theorem nativeActualHighProfileResourceExpansion_leaves_le
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star<U) (hl : star≤as.length) (ops : List NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) (r : ℕ) (hr : st.tree.leaves≤r)
    (Q : NativeActualResourceState S as i star) (hQ : Q∈nativeActualResourceExpansion Γ hs hl ops st) :
    Q.tree.leaves≤r+2*ops.length := by
  induction ops generalizing st r with
  | nil=>
    simp only [nativeActualResourceExpansion,List.mem_cons,List.not_mem_nil,or_false] at hQ
    subst Q
    simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using hr
  | cons op ops ih=>
    simp only [nativeActualResourceExpansion] at hQ
    obtain ⟨V,hV,hQ⟩:=List.mem_flatMap.mp hQ
    have HV:=nativeActualHighProfileResourceStep_leaves_le Γ hs hl op st r hr V hV
    have HQ:=ih V (r+2) HV hQ
    simp only [List.length_cons]
    omega

theorem nativeActualInitialState_high_forkCost_zero (as : List PositiveMass)
    (i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hlen : i≤as.length) (a : ℝ)
    (f : ℕ→ℝ) (hlo : ∀j,j<U→f j=0) :
    (nativeActualInitialState (S:=S) as i star a hlen).tree.forkCost f=0 := by
  change (nativeFreshAtSlot (single (S:=S) as) a (singleSlot as) i).tree.forkCost f=0
  rw [nativeFreshAtSlot_high_forkCost (single as) a (singleSlot as) (hi.trans_lt hs) f hlo,
    single_forkCost]

theorem nativeActualInitialExpansion_high_profile_le (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length) (a : ℝ)
    (ops : List NativeActualExpansionOp) (f : ℕ→ℝ)
    (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((nativeActualResourceExpansion Γ hs (by omega) ops
      (nativeActualInitialState as i star a (by omega))).map (fun Q=>|Q.term.coefficient| *
        (Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
      nativeActualProfileVariation 2 ops*edgeBudget 0 as f := by
  have Hleaves : (nativeActualInitialState (S:=S) as i star a (by omega)).tree.leaves≤2 := by
    have H:=(single (S:=S) as).markedAttach_leaves a _
      (nativeFreshAtSlot_mem (single as) a (singleSlot as) i)
    simpa only [nativeActualInitialState,single_leaves_exact] using H
  have H:=nativeActualResourceExpansion_wholeProfile_le ho Γ hΓ hs (by omega) ops
    (nativeActualInitialState as i star a (by omega)) 2 Hleaves f hf hlo
  rw [nativeActualInitialState_high_forkCost_zero as i star U hi hs (by omega) a f hlo] at H
  simpa only [nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,zero_add] using H

theorem nativeActualConstantExpansion_high_profile_le (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hU : U≤as.length) (ops : List NativeActualExpansionOp)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((nativeActualResourceExpansion Γ hs (by omega) ops (nativeActualConstantState as i star)).map
      (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
      nativeActualProfileVariation 1 ops*edgeBudget 0 as f := by
  have H:=nativeActualResourceExpansion_wholeProfile_le ho Γ hΓ hs (by omega) ops
    (nativeActualConstantState as i star) 1 (by simp only [nativeActualConstantState,single_leaves_exact,le_refl]) f hf hlo
  simpa only [nativeActualConstantState,NativeResourceTerm.ofLive,abs_one,one_mul,single_forkCost,zero_add] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
