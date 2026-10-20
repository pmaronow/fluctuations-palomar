module

public import ComparisonSignedCavityActualResourceExpansion

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

def NativeTargetStarSingleton {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) (star : ℕ) : Prop :=
  ∀c : T.Slot, star < T.splitIndex s c → c=s

theorem native_single_target_star_singleton (as : List PositiveMass)
    (s : (single (S := S) as).Slot) (star : ℕ) :
    NativeTargetStarSingleton (single as) s star := by
  intro c _
  exact (native_single_slot_eq as c).trans (native_single_slot_eq as s).symm

theorem native_fresh_target_star_singleton {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (s : T.Slot) (star : ℕ) :
    NativeTargetStarSingleton (nativeFreshAtSlot T a s star).tree
      (nativeFreshAtSlot T a s star).mark star := by
  intro c hc
  exact nativeFreshAtSlot_unique_fresh_block T a s (U:=star+1) (by omega) c (by omega)

theorem NativeTargetStarSingleton.retain_fresh {as : List PositiveMass}
    {T : ClockTree S as} {s : T.Slot} {star j : ℕ}
    (h : NativeTargetStarSingleton T s star) (a : ℝ) (hj : j ≤ star) :
    NativeTargetStarSingleton (nativeFreshAtSlot T a s j).tree
      ((nativeFreshAtSlot T a s j).embed s) star := by
  intro c hc
  rcases nativeFreshAtSlot_slot_coverage T a s j c with rfl | ⟨d,rfl⟩
  · have HS:=nativeFreshAtSlot_split T a s j s
    rw [(nativeFreshAtSlot T a s j).tree.splitIndex_symm] at hc
    omega
  · rw [(nativeFreshAtSlot_old_splits T a s j).2] at hc
    exact congrArg (nativeFreshAtSlot T a s j).embed (h d hc)

theorem NativePhysicalResourceGenerated.targetStarSingleton
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativePhysicalResourceGenerated i star U seed k T P) (hi : i ≤ star) :
    NativeTargetStarSingleton T P.live.test.target star := by
  induction h with
  | constant as hU=>exact native_single_target_star_singleton as _ star
  | seed as hU a mark hm hl=>
    apply (native_single_target_star_singleton as (singleSlot as) star).retain_fresh a
    rcases hm with rfl | rfl
    · exact hi
    · exact le_rfl
  | freeze h ih=>exact ih
  | reweight h c ih=>exact ih
  | retarget h a ih=>exact native_fresh_target_star_singleton _ a _ star
  | projection h a hl ih=>exact ih.retain_fresh a le_rfl
  | switch h a c hs hh ih=>exact native_fresh_target_star_singleton _ a _ star
  | switchFreshHigh h a j hjU hj hs ih=>
    exact native_fresh_target_star_singleton _ a _ star

theorem NativeActualResourceGenerated.targetStarSingleton
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) :
    NativeTargetStarSingleton T P.live.test.target star := by
  induction h with
  | physical h=>exact h.targetStarSingleton hi
  | freeze h ih=>exact ih
  | reweight h c ih=>exact ih
  | retarget h ih=>exact native_fresh_target_star_singleton _ 0 _ star
  | projection h hl ih=>exact ih.retain_fresh 0 le_rfl
  | markedSwitch h p hp hs hh ih=>exact native_fresh_target_star_singleton _ 0 _ star

theorem NativePhysicalResourceGenerated.highCut_le_length
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativePhysicalResourceGenerated i star U seed k T P) : U≤as.length := by
  induction h with
  | constant as hU=>exact hU
  | seed as hU a mark hm hl=>exact hU
  | freeze h ih=>exact ih
  | reweight h c ih=>exact ih
  | retarget h a ih=>exact ih
  | projection h a hl ih=>exact ih
  | switch h a c hs hh ih=>exact ih
  | switchFreshHigh h a j hjU hj hs ih=>exact ih

theorem NativeActualResourceGenerated.highCut_le_length
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) : U≤as.length := by
  induction h with
  | physical h=>exact h.highCut_le_length
  | freeze h ih=>exact ih
  | reweight h c ih=>exact ih
  | retarget h ih=>exact ih
  | projection h hl ih=>exact ih
  | markedSwitch h p hp hs hh ih=>exact ih

theorem NativeTargetStarSingleton.observed_high_block {as : List PositiveMass}
    {T : ClockTree S as} {s : T.Slot} {star : ℕ}
    (h : NativeTargetStarSingleton T s star) (a : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a) (c : p.tree.Slot)
    (hc : star < p.tree.splitIndex (p.embed s) c) :
    c=p.mark ∨ c=p.embed s := by
  rcases markedAttach_slot_coverage T a p hp c with hmark | ⟨d,rfl⟩
  · exact Or.inl hmark
  · rw [(T.markedAttach_embed_preserves a p hp).2] at hc
    exact Or.inr (congrArg p.embed (h d hc))

theorem nativeActualInitialExpansion_targetStarSingleton
    {i star U : ℕ} {as : List PositiveMass} (a : ℝ) (hi : i ≤ as.length)
    (hiStar : i ≤ star) (hU : U ≤ as.length) (hs : star < U)
    (Γ : ∀st : NativeHighSwitchState S as,MarkedPlacement st.tree → ℝ)
    (ops : List NativeActualExpansionOp)
    (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceExpansion Γ hs (by omega) ops
      (nativeActualInitialState as i star a hi)) :
    NativeTargetStarSingleton Q.tree Q.term.live.test.target star := by
  exact (nativeActualInitialExpansion_valid as i star U hiStar hs hU a Γ ops Q hQ).targetStarSingleton hiStar

theorem native_eq_single_of_slots_singleton {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (h : ∀c : T.Slot,c=s) : T=single as := by
  induction T with
  | leaf=>rfl
  | step b T ih=>exact congrArg (fun V=>V.step b) (ih s h)
  | fork T V ihT ihV=>
    have H:Sum.inl (nativeFirstSlot T)=Sum.inr (nativeFirstSlot V):=
      (h (Sum.inl (nativeFirstSlot T))).trans (h (Sum.inr (nativeFirstSlot V))).symm
    exact (Sum.inl_ne_inr H).elim

end OAI.SKFluctuations.Hierarchy.ClockTree
