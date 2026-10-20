module

public import ComparisonSignedCavityActualSingleForestLaw
public import CavityRestMarkedExchange
public import ComparisonSignedCavityForestFullFreshRestTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type}

def nativeReplaceAtSlot : {as : List PositiveMass} → (T : ClockTree S as) →
    T.Slot → T.Assignment → S → T.Assignment
  | _,.leaf,_,_,u=>u
  | _,.step _ T,s,σ,u=>nativeReplaceAtSlot T s σ u
  | _,.fork T V,s,σ,u=>match s with
    | Sum.inl s=>(nativeReplaceAtSlot T s σ.1 u,σ.2)
    | Sum.inr s=>(σ.1,nativeReplaceAtSlot V s σ.2 u)

theorem nativeReplaceAtSlot_at {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (σ : T.Assignment) (u : S) (c : T.Slot) :
    T.atSlot (nativeReplaceAtSlot T s σ u) c=if c=s then u else T.atSlot σ c := by
  classical
  induction T with
  | leaf=>cases s;cases c;simp [nativeReplaceAtSlot,atSlot]
  | step b T ih=>exact ih s σ c
  | fork T V ihT ihV=>
    cases s <;> cases c <;> simp only [nativeReplaceAtSlot,atSlot,Sum.elim_inl,
      Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,ite_false]
    · exact ihT _ _ _
    · exact ihV _ _ _

variable {ι : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_single_full_rest_whole_exchange
    (as : List PositiveMass) {w : S → ℝ} (hw : ∀σ,0<w σ)
    (φ : S → (ι → ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement (single (S:=S×B) as)) (hp : p∈(single as).markedAttach a)
    (q : ℕ → ι → ℝ≥0)
    (Q : (single (S:=S×B) as).cavityLeft.Assignment → S → ℝ) (x : ι → ℝ) :
    p.tree.cavityLeft.expect w φ q (fun σ=>Q (p.restRestrict σ) (p.restSpin σ)) x=
    p.tree.cavityLeft.expect w φ q (fun σ=>Q
      (nativeReplaceAtSlot (single (S:=S×B) as).cavityLeft
        ((single (S:=S×B) as).cavityLeftSlot (singleSlot as))
        (p.restRestrict σ) (p.restSpin σ))
      ((single (S:=S×B) as).cavityLeft.atSlot (p.restRestrict σ)
        ((single (S:=S×B) as).cavityLeftSlot (singleSlot as)))) x := by
  let C:=fun u:S=>assignmentOfSlots (single (S:=S×B) as).cavityLeft (fun _=>u)
  have hAll : ∀c : (single (S:=S×B) as).cavityLeft.Slot,
      c=(single (S:=S×B) as).cavityLeftSlot (singleSlot as) := by
    intro c
    obtain ⟨d,rfl⟩:=(single (S:=S×B) as).cavityLeftSlot.surjective c
    exact congrArg (single (S:=S×B) as).cavityLeftSlot (native_single_slot_eq as d)
  have hOld : ∀σ,p.restRestrict σ=C
      ((single (S:=S×B) as).cavityLeft.atSlot (p.restRestrict σ)
        ((single (S:=S×B) as).cavityLeftSlot (singleSlot as))) := by
    intro σ
    apply (single (S:=S×B) as).cavityLeft.assignment_ext
    intro c
    rw [atSlot_assignmentOfSlots,hAll c]
  have hNew : ∀σ,nativeReplaceAtSlot (single (S:=S×B) as).cavityLeft
      ((single (S:=S×B) as).cavityLeftSlot (singleSlot as)) (p.restRestrict σ) (p.restSpin σ)=
      C (p.restSpin σ) := by
    intro σ
    apply (single (S:=S×B) as).cavityLeft.assignment_ext
    intro c
    rw [nativeReplaceAtSlot_at,atSlot_assignmentOfSlots,ite_eq_left (hAll c)]
  have H:=single_full_rest_exchange hw φ as ho p hp q (fun u v=>Q (C u) v) x
  simp_rw [p.restRestrict_at] at hOld
  simp_rw [hNew]
  simp_rw [p.restRestrict_at]
  simp_rw [hOld]
  simpa only [MarkedPlacement.restSpin] using H

theorem native_target_singleton_full_rest_exchange
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (k : ℕ)
    (h : ∀c : T.Slot,k≤T.splitIndex s c → c=s)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hh : k≤p.tree.splitIndex (p.embed s) p.mark)
    (q : ℕ → ι → ℝ≥0) (Q : T.cavityLeft.Assignment → S → ℝ) (x : ι → ℝ) :
    p.tree.cavityLeft.expect w φ q (fun σ=>Q (p.restRestrict σ) (p.restSpin σ)) x=
    p.tree.cavityLeft.expect w φ q (fun σ=>Q
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) (p.restSpin σ))
      (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s))) x := by
  induction T generalizing a k q x with
  | leaf=>
    cases s
    simpa only [single,singleSlot,cavityLeftSlot,cavityLeft,atSlot,nativeReplaceAtSlot] using
      native_single_full_rest_whole_exchange [] hw φ ho p hp q Q x
  | @step b tail T ih=>
    cases k with
    | zero=>
      have hT:=native_eq_single_of_slots_singleton (T.step b) s (fun c=>h c (Nat.zero_le _))
      have hT0 : T=single tail := by injection hT with hT0
      subst T
      have hs:=native_single_slot_eq (b::tail) s
      subst s
      exact native_single_full_rest_whole_exchange (b::tail) hw φ ho p hp q Q x
    | succ k=>
      rcases List.mem_cons.mp hp with rfl | hp
      · change k+1≤0 at hh
        omega
      · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
        have hi : ∀c:T.Slot,k≤T.splitIndex s c → c=s := by
          intro c hc
          exact h c (by change k+1≤1+T.splitIndex s c;omega)
        have hh' : k≤r.tree.splitIndex (r.embed s) r.mark := by
          change k+1≤1+r.tree.splitIndex (r.embed s) r.mark at hh
          omega
        change (r.tree.cavityLeft.step b).expect w φ q
          (fun σ=>Q (r.restRestrict σ) (r.restSpin σ)) x=
          (r.tree.cavityLeft.step b).expect w φ q (fun σ=>Q
            (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (r.restRestrict σ) (r.restSpin σ))
            (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot s))) x
        rw [expect_step hw φ b _ ho.2.2,expect_step hw φ b _ ho.2.2]
        congr 1
        funext y
        exact ih s k hi ho.2.2 r hr hh' (fun j=>q (j+1)) Q y
  | @fork tail T V ihT ihV=>
    cases k with
    | zero=>
      have H:Sum.inl (nativeFirstSlot T)=Sum.inr (nativeFirstSlot V):=
        (h _ (Nat.zero_le _)).trans (h _ (Nat.zero_le _)).symm
      exact (Sum.inl_ne_inr H).elim
    | succ k=>
      rcases List.mem_cons.mp hp with rfl | hp
      · change k+1≤0 at hh
        omega
      · rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
          cases s with
          | inr s=>change k+1≤0 at hh;omega
          | inl s=>
            have hi : ∀c:T.Slot,k+1≤T.splitIndex s c → c=s := by
              intro c hc
              exact Sum.inl.inj (h (Sum.inl c) hc)
            have hh' : k+1≤r.tree.splitIndex (r.embed s) r.mark:=hh
            simp_rw [MarkedPlacement.restRestrict_left,MarkedPlacement.restSpin_left]
            change (r.tree.cavityLeft.fork V.cavityLeft).expect w φ q
              (fun σ=>Q (r.restRestrict σ.1,σ.2) (r.restSpin σ.1)) x=
              (r.tree.cavityLeft.fork V.cavityLeft).expect w φ q (fun σ=>Q
                (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (r.restRestrict σ.1)
                  (r.restSpin σ.1),σ.2)
                (T.cavityLeft.atSlot (r.restRestrict σ.1) (T.cavityLeftSlot s))) x
            rw [expect_fork,expect_fork]
            conv_lhs=>rw [native_expect_nested_commute]
            conv_rhs=>rw [native_expect_nested_commute]
            congr 1
            funext τ
            exact ihT s (k+1) hi ho r hr hh' q (fun σ u=>Q (σ,τ) u) x
        · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
          cases s with
          | inl s=>change k+1≤0 at hh;omega
          | inr s=>
            have hi : ∀c:V.Slot,k+1≤V.splitIndex s c → c=s := by
              intro c hc
              exact Sum.inr.inj (h (Sum.inr c) hc)
            have hh' : k+1≤r.tree.splitIndex (r.embed s) r.mark:=hh
            simp_rw [MarkedPlacement.restRestrict_right,MarkedPlacement.restSpin_right]
            change (T.cavityLeft.fork r.tree.cavityLeft).expect w φ q
              (fun σ=>Q (σ.1,r.restRestrict σ.2) (r.restSpin σ.2)) x=
              (T.cavityLeft.fork r.tree.cavityLeft).expect w φ q (fun σ=>Q
                (σ.1,nativeReplaceAtSlot V.cavityLeft (V.cavityLeftSlot s) (r.restRestrict σ.2)
                  (r.restSpin σ.2))
                (V.cavityLeft.atSlot (r.restRestrict σ.2) (V.cavityLeftSlot s))) x
            rw [expect_fork,expect_fork]
            congr 1
            funext τ
            exact ihV s (k+1) hi ho r hr hh' q (fun σ u=>Q (τ,σ) u) x

end OAI.SKFluctuations.Hierarchy.ClockTree
