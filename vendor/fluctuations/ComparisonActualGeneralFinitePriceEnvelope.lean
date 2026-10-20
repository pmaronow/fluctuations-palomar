module

public import ComparisonActualGeneralFourSummability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter
open scoped Topology
set_option maxHeartbeats 12000000

 theorem exists_uniform_positive_finite_level_price_envelope
    (depth : ℕ) (P : ℕ→ℝ→ℕ→Prop)
    (Hprice : ∀j < depth,∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,P j C n)
    (Hmono : ∀j C C' n,C ≤ C' → P j C n → P j C' n) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,∀j < depth,P j C n := by
  induction depth with
  | zero=>exact ⟨1,zero_lt_one,Eventually.of_forall (by intro n j hj;omega)⟩
  | succ depth ih=>
    obtain ⟨Cp,hCp,HP⟩:=ih (fun j hj=>Hprice j (by omega))
    obtain ⟨Cj,hCj,Hj⟩:=Hprice depth (by omega)
    refine ⟨Cp+Cj,by positivity,?_⟩
    filter_upwards [HP,Hj] with n hnP hnJ
    intro j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt|rfl
    · exact Hmono j Cp (Cp+Cj) n (by linarith) (hnP j hlt)
    · exact Hmono j Cj (Cp+Cj) n (by linarith) hnJ

end OAI.SKFluctuations.Cavity
