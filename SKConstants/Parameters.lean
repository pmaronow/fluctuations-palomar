module

public import SKConstants.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Tauto

public section
namespace SKConstants

theorem family_feasible {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hsmall : ε < 1 / 1000) (hgap : 10 * ε < 1 / 4 - c) :
    Feasible c (family ε) := by
  unfold Feasible family
  dsimp
  repeat' constructor
  all_goals linarith

theorem explicit_feasible : Feasible (2 / 9) explicitParameters := by
  norm_num [Feasible, explicitParameters]

theorem feasible_below_quarter (c : ℝ) (hc : 0 < c) (hquarter : c < 1 / 4) :
    ∃ p : Parameters, Feasible c p := by
  have hgap : 0 < (1 / 4 - c) / 10 := by linarith
  have hmin : 0 < min (1 / 1000 : ℝ) ((1 / 4 - c) / 10) :=
    lt_min (by norm_num) hgap
  obtain ⟨ε, hε, hupper⟩ := exists_between hmin
  exact ⟨family ε, family_feasible hc hε
    (lt_of_lt_of_le hupper (min_le_left _ _))
    (by have := lt_of_lt_of_le hupper (min_le_right _ _); linarith)⟩

theorem feasible_implies_below_quarter {c : ℝ} {p : Parameters}
    (h : Feasible c p) : c < 1 / 4 := by
  unfold Feasible at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58⟩
  linarith

theorem feasible_iff (c : ℝ) :
    (∃ p : Parameters, Feasible c p) ↔ 0 < c ∧ c < 1 / 4 := by
  constructor
  · rintro ⟨p, h⟩
    refine ⟨?_, feasible_implies_below_quarter h⟩
    unfold Feasible at h
    tauto
  · rintro ⟨hc, hquarter⟩
    exact feasible_below_quarter c hc hquarter

end SKConstants
