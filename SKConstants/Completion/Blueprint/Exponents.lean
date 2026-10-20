module

public import SKConstants.Defs
public import SKConstants.SKSparseBoundaryRate

@[expose] public section
noncomputable section
open Filter
open scoped Topology

namespace SKConstants.Blueprint

def FineExponents (p : Parameters) : Prop :=
  p.f / 4 < p.a ∧ p.a + p.f / 2 < 1 ∧ 0 < p.kf ∧ p.kf < p.a ∧ p.kf < p.f ∧ p.kf < 1 - p.a

def CoarseExponents (p : Parameters) : Prop :=
  0 < p.b ∧ p.b < p.f ∧ 0 < p.z ∧ 0 < p.gamma ∧ 0 < p.kb ∧ p.kb < p.z ∧
    p.kb < 2 * p.gamma ∧ p.kb < p.a ∧ p.kb < p.b ∧ 2 * p.z < p.sb ∧
    2 * p.gamma + p.b / 2 < p.sb ∧ p.a < 1 - p.sb

def BoundaryExponents (p : Parameters) : Prop :=
  0 < p.q ∧ p.q < p.uField ∧ p.uField < p.r ∧ p.r < 1 ∧ 2 * p.uField - p.r < p.q ∧ p.q < 1 / 2

def SequenceExponents (p : Parameters) (sseq : ℝ) : Prop :=
  p.r < p.sb ∧ p.q < p.sb ∧ p.a < p.grid ∧ p.grid < 1 - p.sb ∧ p.sb < sseq ∧
    p.r < p.b / 2 ∧ p.q < p.kb ∧ p.q < p.D ∧ p.q < p.zP ∧ 0 < p.zP ∧ p.zP < 1 / 2 ∧ 0 < p.D

def CoverageExponents (p : Parameters) (sseq : ℝ) : Prop :=
  0 < p.d ∧ p.e + p.d < p.uEnt ∧ p.uEnt < p.D ∧ p.uEnt < p.kf - p.D ∧ sseq < p.e ∧
    p.d < 1 - sseq

def Admissible (c sseq : ℝ) (p : Parameters) : Prop :=
  FineExponents p ∧ CoarseExponents p ∧ BoundaryExponents p ∧ SequenceExponents p sseq ∧
    CoverageExponents p sseq ∧ 0 < c ∧ c < p.q

def g0Parameters : Parameters where
  a := 1 / 2
  f := 1 / 2
  kf := 12 / 25
  D := 6 / 25
  uEnt := 23 / 100
  d := 1 / 200
  e := 11 / 50
  zP := 3 / 10
  b := 1 / 5
  z := 2 / 25
  gamma := 9 / 200
  kb := 7 / 100
  sb := 1 / 5
  r := 9 / 100
  uField := 7 / 100
  sField := 11 / 200
  q := 3 / 50
  grid := 3 / 5

def g0Sequence : ℝ := 21 / 100

theorem g0_admissible : Admissible (1 / 20) g0Sequence g0Parameters := by
  unfold Admissible FineExponents CoarseExponents BoundaryExponents SequenceExponents
    CoverageExponents g0Parameters g0Sequence
  norm_num

theorem g0_feasible : Feasible (1 / 20) g0Parameters := by
  unfold Feasible g0Parameters
  norm_num

theorem g0_supplements :
    let p := g0Parameters
    p.f / 4 < p.a ∧ p.a + p.f / 2 < 1 ∧ 2 * p.a + p.f / 2 - 1 < 1 - p.kf ∧
    2 * p.z < p.sb ∧ 2 * p.gamma + p.b / 2 < p.sb ∧ p.a + 2 * p.gamma + p.b / 2 < 1 ∧
    p.kb < p.b ∧ p.kb < p.a ∧ p.z < 2 * p.gamma ∧ p.kb < p.z ∧ p.kb < p.D ∧ p.kb < p.zP ∧
    2 * p.uField - p.r < p.q ∧ p.r < p.sb ∧ p.q < p.sb ∧ p.e + p.d < p.uEnt ∧
    p.uEnt < p.D ∧ p.uEnt < p.kf - p.D ∧ p.grid + 2 * p.gamma + p.b / 2 < 1 ∧
    p.grid + 2 * p.z < 1 ∧ p.grid + p.r < 1 ∧ p.grid + p.q < 1 ∧ p.sb < g0Sequence ∧
    g0Sequence < p.e ∧ (1 / 20 : ℝ) < p.q := by
  simp only [g0Parameters, g0Sequence]
  norm_num

theorem two_rpow_le_small_rpow (a b c C D ε : ℝ) (hac : a < c) (hbc : b < c)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a + D * (n : ℝ) ^ b ≤ ε * (n : ℝ) ^ c := by
  filter_upwards [constant_rpow_le_small_rpow a c C (ε / 2) hac hC (by positivity),
    constant_rpow_le_small_rpow b c D (ε / 2) hbc hD (by positivity)] with n h1 h2
  linarith

end SKConstants.Blueprint
