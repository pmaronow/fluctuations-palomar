module

public import ComparisonSignedCavityActualResourceFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualHighExpansion_coefficient_variation_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (k : ℕ)
    (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r) :
    ((nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) st).map
      (fun Q=>|Q.term.coefficient|)).sum ≤
        |st.term.coefficient| *nativeHighSwitchForkVariation r k := by
  induction k generalizing st r with
  | zero=>simp [nativeActualResourceExpansion,nativeHighSwitchForkVariation]
  | succ k ih=>
    let C := nativeHighSwitchForkVariation (r+2) k
    have hC : 0≤C := nativeHighSwitchForkVariation_nonneg _ _
    rw [List.replicate_succ,nativeActualResourceExpansion]
    simp only [List.map_flatMap,native_sum_flatMap]
    unfold nativeActualResourceStep
    simp only [List.map_flatMap,native_sum_flatMap]
    have Hrow (p : {p // p∈st.tree.markedAttach 0}) :
        ((if hh : U≤p.val.tree.splitIndex (p.val.embed st.term.live.test.target) p.val.mark then
          [st.markedRow Γ p.val p.property hs hh] else []).map
            (fun t=>((nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) t).map
              (fun Q=>|Q.term.coefficient|)).sum)).sum ≤
          |p.val.coeff| *(|st.term.coefficient| *C) := by
      split_ifs with hh
      · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
        have hleaves : (st.markedRow Γ p.val p.property hs hh).tree.leaves≤r+2 := by
          have h1:=st.tree.markedAttach_leaves 0 p.val p.property
          have h2:=p.val.tree.markedAttach_leaves 0
            (nativeFreshAtSlot p.val.tree 0 (p.val.embed st.term.live.test.target) star)
            (nativeFreshAtSlot_mem p.val.tree 0 (p.val.embed st.term.live.test.target) star)
          change (nativeFreshAtSlot p.val.tree 0 (p.val.embed st.term.live.test.target) star).tree.leaves≤r+2
          omega
        apply (ih _ hleaves).trans
        rw [NativeActualResourceState.markedRow_coefficient,abs_mul,abs_mul]
        have HG:=mul_le_mul_of_nonneg_left (hΓ st.toHigh p.val p.property)
          (show 0≤|p.val.coeff| *|st.term.coefficient| *C by positivity)
        convert HG using 1 <;> ring
      · simpa only [List.map_nil,List.sum_nil] using
          (show 0≤|p.val.coeff| *(|st.term.coefficient| *C) by positivity)
    apply (List.sum_le_sum (fun p _=>Hrow p)).trans
    rw [List.sum_map_mul_right]
    have HE : ((st.tree.markedAttach 0).attach.map (fun p=>|p.val.coeff|)).sum=
        2*(st.tree.leaves:ℝ) := by
      calc
        _=((st.tree.markedAttach 0).map (fun p=>|p.coeff|)).sum := by
          conv_rhs=>rw [←List.attach_map_val]
        _=_ := by simpa only [sub_zero] using st.tree.markedAttach_variation ho
    rw [HE]
    have hr' : (st.tree.leaves:ℝ)≤r := by exact_mod_cast hr
    have HC : 2*(st.tree.leaves:ℝ)≤4*(r:ℝ)+1 := by
      have hr0 : (0:ℝ)≤r := Nat.cast_nonneg _
      linarith
    have H:=mul_le_mul_of_nonneg_right HC
      (show 0≤|st.term.coefficient| *C by positivity)
    simpa only [nativeHighSwitchForkVariation,C,mul_assoc,mul_left_comm,mul_comm] using H

theorem nativeActualHighExpansion_generation
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (k : ℕ)
    (st Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) st) :
    Q.generation=st.generation+k := by
  induction k generalizing st with
  | zero=>
    obtain rfl:=List.mem_singleton.mp hQ
    simp
  | succ k ih=>
    rw [List.replicate_succ,nativeActualResourceExpansion] at hQ
    obtain ⟨t,ht,hQ⟩:=List.mem_flatMap.mp hQ
    have HG:=ih t hQ
    unfold nativeActualResourceStep at ht
    obtain ⟨p,hp,ht⟩:=List.mem_flatMap.mp ht
    split_ifs at ht with hh
    · obtain rfl:=List.mem_singleton.mp ht
      change Q.generation=(st.generation+1)+k at HG
      omega
    · cases ht

theorem nativeActualHighExpansion_terminal_abs_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (k : ℕ)
    (st : NativeActualResourceState S as i star)
    (F : NativeActualResourceState S as i star → ℝ) {B : ℝ} (hB : 0≤B)
    (hF : ∀Q∈nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) st,
      |F Q|≤|Q.term.coefficient| *B) :
    |((nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) st).map F).sum| ≤
      |st.term.coefficient| *nativeHighSwitchForkVariation st.tree.leaves k*B := by
  let L:=nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) st
  have Habs : |(L.map F).sum|≤(L.map (fun Q=>|F Q|)).sum := by
    induction L with
    | nil=>simp
    | cons Q L ih=>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)
  have Hsum := List.sum_le_sum (fun Q hQ=>hF Q hQ)
  have Hvar := mul_le_mul_of_nonneg_right
    (nativeActualHighExpansion_coefficient_variation_le ho Γ hΓ hs hl k st (le_refl _)) hB
  exact Habs.trans (Hsum.trans (by simpa only [List.sum_map_mul_right] using Hvar))

end OAI.SKFluctuations.Hierarchy.ClockTree
