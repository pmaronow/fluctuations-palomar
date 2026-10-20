module

public import Mathlib.Basic.Real.Basic

public section
noncomputable section
namespace SKConstants

structure Parameters where
  a : ℝ
  f : ℝ
  kf : ℝ
  D : ℝ
  uEnt : ℝ
  d : ℝ
  e : ℝ
  zP : ℝ
  b : ℝ
  z : ℝ
  gamma : ℝ
  kb : ℝ
  sb : ℝ
  r : ℝ
  uField : ℝ
  sField : ℝ
  q : ℝ
  grid : ℝ

@[expose] def Feasible (c : ℝ) (p : Parameters) : Prop :=
  0 < p.a ∧
  0 < p.f ∧
  0 < p.kf ∧
  0 < p.D ∧
  0 < p.uEnt ∧
  0 < p.d ∧
  0 < p.e ∧
  0 < p.zP ∧
  0 < p.b ∧
  0 < p.z ∧
  0 < p.gamma ∧
  0 < p.kb ∧
  0 < p.sb ∧
  0 < p.r ∧
  0 < p.uField ∧
  0 < p.sField ∧
  0 < p.q ∧
  0 < p.grid ∧
  0 < c ∧
  p.kf < p.a ∧
  p.kf < p.f ∧
  p.kf < 1 - p.a ∧
  p.a + p.f / 2 < 1 ∧
  p.kb < p.a ∧
  p.z < p.a ∧
  p.kb < p.z ∧
  p.kb < p.b / 2 ∧
  p.z < p.b / 2 ∧
  p.z < 2 * p.gamma ∧
  2 * p.z - p.a < p.sb ∧
  2 * p.z - 2 * p.gamma < p.sb ∧
  p.z < p.sb ∧
  p.b / 2 < p.sb ∧
  2 * p.gamma < p.sb ∧
  p.gamma + p.b / 4 < p.sb ∧
  p.a < 1 - p.sb ∧
  p.b < p.f ∧
  p.uEnt < p.D ∧
  p.uEnt < p.kf - p.D ∧
  p.e < p.uEnt - p.d ∧
  p.e < 1 ∧
  p.r < p.b / 2 ∧
  p.q < p.uField ∧
  p.uField < p.r ∧
  2 * p.uField - p.r < p.sField ∧
  p.sField < p.q ∧
  p.q < p.kb ∧
  p.q < p.D ∧
  p.q < p.zP ∧
  p.zP < 1 / 2 ∧
  p.q < p.e ∧
  p.sb < p.e ∧
  p.r < p.e ∧
  p.a < p.grid ∧
  p.grid < 1 - p.sb ∧
  p.grid < 1 - p.q ∧
  p.grid < 1 - p.r ∧
  c < p.q ∧
  p.q < 1 / 2

@[expose] def family (ε : ℝ) : Parameters where
  a := 1 / 2
  f := 1 / 2
  kf := 1 / 2 - 2 * ε
  D := 1 / 4 - ε
  uEnt := 1 / 4 - 2 * ε
  d := ε / 2
  e := 1 / 4 - 3 * ε
  zP := 3 / 10
  b := 1 / 2 - 14 * ε
  z := 1 / 4 - 8 * ε
  gamma := 1 / 8 - 3 * ε
  kb := 1 / 4 - 9 * ε
  sb := 1 / 4 - 5 * ε
  r := 1 / 4 - 15 / 2 * ε
  uField := 1 / 4 - 39 / 4 * ε
  sField := 1 / 4 - 21 / 2 * ε
  q := 1 / 4 - 10 * ε
  grid := 3 / 5

@[expose] def explicitParameters : Parameters where
  a := 49 / 100
  f := 49 / 100
  kf := 489 / 1000
  D := 489 / 2000
  uEnt := 61 / 250
  d := 1 / 2000
  e := 243 / 1000
  zP := 3 / 10
  b := 9 / 20
  z := 447 / 2000
  gamma := 141 / 1250
  kb := 2233 / 10000
  sb := 57 / 250
  r := 281 / 1250
  uField := 1119 / 5000
  sField := 2229 / 10000
  q := 223 / 1000
  grid := 11 / 20

end SKConstants
