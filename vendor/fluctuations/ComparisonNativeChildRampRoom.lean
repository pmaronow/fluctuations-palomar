module

public import ConcreteRampBudgets
public import ConcreteDownwardRampBudgets
public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonPolynomialRoom

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

theorem comparison_upward_ramp_speed_room {N delta U L E d y a b q:ℝ}
    (hN:0 < N) (hU:0 < U) (hL:0 < L) (hLU:L ≤ U)
    (hE:0 < E) (hd:0 ≤ d) (hy:0 < y) (hq:0 < q)
    (hwidth:q*y ≤ b-a) (hpower:1 ≤ N^delta)
    (hroom:1+2/q ≤ N^(3*delta)) :
    (comparisonCap N delta U L E d 0)⁻¹+2*y/(b-a) ≤
      (N^(2*delta)*U)^2/(N^delta*U^2) := by
  have hgap:0 < b-a:=(mul_pos hq hy).trans_le hwidth
  have hspeed:2*y/(b-a) ≤ 2/q:=by
    have hh:=div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*y) (mul_pos hq hy) hwidth
    have he:2*y/(q*y)=2/q:=by field_simp
    rwa [he] at hh
  have hzero:(comparisonCap N delta U L E d 0)⁻¹ ≤ 1:=
    (comparisonCap_zero_inverse_le (δ:=delta) hN hU hL hLU hE hd).trans
      (inv_le_one_of_one_le₀ hpower)
  rw [comparisonFloor_reciprocal_square_room hN hU]
  have he:(N^delta)^3=N^(3*delta):=by
    rw [←Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  rw [he]
  exact (add_le_add hzero hspeed).trans hroom

theorem eventually_comparison_native_upward_ramp_room
    {gamma D m delta cScale q:ℝ}
    (hgamma:0 < gamma) (hm:0 < m) (hdelta:0 < delta)
    (hcScale:0 < cScale) (hq:0 < q) :
    ∀ᶠ n:ℕ in atTop,∀ E d y a b:ℝ,
      0 < E → 0 < d → d ≤ D →
      Real.sqrt (n:ℝ)*E ≤ d^2 → gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E →
      cScale*comparisonLowerScale n E d ≤ y → q*y ≤ b-a →
      let U:=comparisonSmallMass n E
      let L:=comparisonConstraintLength n E d
      let M:=comparisonCap n delta U L E d
      inverseCapPrimitive M 1 ≤ y/4 ∧
      (M 0)⁻¹+2*y/(b-a) ≤ ((n:ℝ)^(2*delta)*U)^2/((n:ℝ)^delta*U^2) := by
  have hC:0 < 1/gamma:=by positivity
  have htravel:=eventually_comparisonTravel_small (C:=1/gamma) (D:=D)
    (m:=m) (δ:=delta) (ε:=cScale/4) hC (by linarith) (by positivity)
  have hp:Tendsto (fun n:ℕ=>(n:ℝ)^delta) atTop atTop:=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hp3:Tendsto (fun n:ℕ=>(n:ℝ)^(3*delta)) atTop atTop:=
    (tendsto_rpow_atTop (by positivity : 0 < 3*delta)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htravel,hp.eventually (eventually_ge_atTop (1:ℝ)),
    hp3.eventually (eventually_ge_atTop (1+2/q:ℝ)),eventually_gt_atTop (0:ℕ)] with n hn hpow hroom hn0
  intro E d y a b hE hd hdD hupper hlower hscale hwidth
  have hN:0 < (n:ℝ):=by exact_mod_cast hn0
  have hU:=comparisonSmallMass_pos hN hE
  have hL:=comparisonConstraintLength_pos hN hE hd
  have ha0:=comparisonLowerScale_pos hN hE hd
  have hy:0 < y:=(mul_pos hcScale ha0).trans_le hscale
  have hlower':(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ (1/gamma)*E:=by
    have hh:=mul_le_mul_of_nonneg_left hlower (show 0 ≤ 1/gamma by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hgamma.ne',one_mul] using hh
  have hh:=hn E d hE hd hdD hupper hlower'
  have hprimitive:=comparisonCapPrimitive_le_log (δ:=delta) hN hU hL hE hd.le
  have hscale':(cScale/4)*comparisonLowerScale n E d ≤ y/4:=by linarith
  refine ⟨hprimitive.trans (hh.trans hscale'),?_⟩
  exact comparison_upward_ramp_speed_room hN hU hL (min_le_left _ _) hE hd.le hy hq hwidth hpow hroom

theorem eventually_comparison_native_downward_ramp_room
    {gamma m delta cScale q:ℝ}
    (hgamma:0 < gamma) (hm:0 < m) (hdelta:0 < delta)
    (hcScale:0 < cScale) (hq:0 < q) :
    ∀ᶠ n:ℕ in atTop,∀ E d y:ℝ,
      0 < E → 0 < d → Real.sqrt (n:ℝ)*E ≤ d^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E → cScale*comparisonLowerScale n E d ≤ y →
      reciprocalFloorTime ((n:ℝ)^delta*(comparisonSmallMass n E)^2)
        ((n:ℝ)^(2*delta)*comparisonSmallMass n E) 1 ≤ q*y := by
  have hC:0 < 1/gamma:=by positivity
  have hsmall:=eventually_comparisonSmallMass_small (C:=1/gamma) (m:=m)
    (ε:=q*cScale) hC hm (by positivity)
  have hp:Tendsto (fun n:ℕ=>(n:ℝ)^delta) atTop atTop:=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall,hp.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (0:ℕ)] with n hn hpow hn0
  intro E d y hE hd hupper hlower hscale
  have hN:0 < (n:ℝ):=by exact_mod_cast hn0
  have hU:=comparisonSmallMass_pos hN hE
  have hlower':(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ (1/gamma)*E:=by
    have hh:=mul_le_mul_of_nonneg_left hlower (show 0 ≤ 1/gamma by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hgamma.ne',one_mul] using hh
  have hh:=hn E d hE hd hupper hlower'
  have hmass:comparisonSmallMass n E ≤ q*y:=by
    have hs:=mul_le_mul_of_nonneg_left hscale hq.le
    nlinarith
  exact (comparisonFloor_total_time_le (δ:=delta) hN hU).trans
    ((div_le_self hU.le hpow).trans hmass)

end OAI.SKFluctuations.LaplaceWindowFormalization
