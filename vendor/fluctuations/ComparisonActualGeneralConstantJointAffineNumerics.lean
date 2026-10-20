module

public import ComparisonActualGeneralConstantJointFourNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

 theorem actual_general_constant_joint_source_affine_bound_of_cubic_four_prices
    {n : ℕ} {as : List PositiveMass} {star U : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp d cK q Co Cf Cfr Ct Cc : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hd : 0 < d) (hd1 : d ≤ 1) (hcK : 0 < cK) (hq : 0 ≤ q)
    (hCo : 0 ≤ Co) (hCf : 0 ≤ Cf) (hCfr : 0 ≤ Cfr) (hCt : 0 ≤ Ct) (_hCc : 0 ≤ Cc)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*d ≤ nativeContinuumMixedClock n bf hf as star)
    (depth : ℕ)
    (Hpair : ∀j < depth,|actualGeneralFourPairSum bf hf U d
      (actualGeneralFourCenteredForest bf hf hs hU d j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))| ≤ q*d)
    (Hother : ∀j < depth,|actualGeneralFourOtherSourceErrorSum bf hf U d
      (actualGeneralFourCenteredForest bf hf hs hU d j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))| ≤ Co*d^3)
    (Hfirst : ∀j < depth,|actualGeneralFourFirstHighErrorSum bf hf U d
      (actualGeneralFourCenteredForest bf hf hs hU d j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))| ≤ Cf*d^2)
    (Hfrozen : ∀j < depth,|actualGeneralFourFrozenChildSum bf hf hs hU d
      (actualGeneralFourCenteredForest bf hf hs hU d j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))| ≤ Cfr*d^4)
    (Hterminal : |((actualGeneralFourCenteredForest bf hf hs hU d depth
      (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU)).map
        (actualGeneralFourStateResponse bf hf U d)).sum| ≤ Ct*d^3)
    (Hcorrection : |actualGeneralConstantSourceFrozenCorrection (n:=n) bf hf as star U hs hU d| ≤ Cc*d^3) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let den:=Real.exp (-4*Temp)*cK
    |actualGeneralConstantJointSource (n:=n) bf hf as star U| ≤
      |1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *(Temp*(depth:ℝ)/den)*q*d+
        (Temp*(depth:ℝ)*(Co/den+Cf+Cfr)+Temp*Ct+Cc)*d^3 := by
  dsimp only
  let den:=Real.exp (-4*Temp)*cK
  let b:=(bf (partitionPoint 0 as star):ℝ)
  let defect:=|1-b*(scalarTerminal.schedule (scalarBoundaryClocks as
    (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2|
  let F:=(defect*q*d+Co*d^3)/(den*d)+Cfr*d^4+Cf*d^2
  have hden : 0 < den:=by dsimp only [den];positivity
  have hb0 : 0 ≤ b:=NNReal.coe_nonneg _
  have hb : b ≤ Temp:=by
    have H:=htotal _ (partitionPoint_mem as ho star)
    linarith [NNReal.coe_nonneg (hf (partitionPoint 0 as star))]
  have hTemp : 0 ≤ Temp:=hb0.trans hb
  have hdefect : 0 ≤ defect:=abs_nonneg _
  have hF : 0 ≤ F:=by dsimp only [F];positivity
  have HH:=actual_general_constant_joint_source_abs_le_of_four_budgets (n:=n) bf hf hbf hhf htotal
    hd hcK ho hs hU hstarK depth (fun _=>q*d) (fun _=>Co*d^3)
    (fun _=>Cf*d^2) (fun _=>Cfr*d^4) Hpair Hother Hfirst Hfrozen Hterminal
  dsimp only at HH
  simp only [List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul] at HH
  have H0 : |actualGeneralConstantJointSource (n:=n) bf hf as star U| ≤
      b*d*((depth:ℝ)*F+Ct*d^3)+Cc*d^3:=by
    apply HH.trans
    have HX:=add_le_add (le_refl (b*d*((depth:ℝ)*F+Ct*d^3))) Hcorrection
    convert HX using 1
    dsimp only [den,b,defect,F]
    ring
  have Hd42 : d^4 ≤ d^2:=by
    have H2:=pow_le_pow_left₀ hd.le hd1 2
    norm_num only [one_pow] at H2
    have H:=mul_le_mul_of_nonneg_right H2 (sq_nonneg d)
    nlinarith only [H]
  have HFd : F ≤ defect*q/den+(Co/den+Cf+Cfr)*d^2:=by
    have HE : F=defect*q/den+Co/den*d^2+Cfr*d^4+Cf*d^2:=by
      dsimp only [F]
      field_simp [hden.ne',hd.ne']
    rw [HE]
    have H:=mul_le_mul_of_nonneg_left Hd42 hCfr
    nlinarith only [H]
  have Hprefactor : b*d ≤ Temp*d:=mul_le_mul_of_nonneg_right hb hd.le
  have Hinner : 0 ≤ (depth:ℝ)*F+Ct*d^3:=by positivity
  have H1:=H0.trans (add_le_add
    (mul_le_mul_of_nonneg_right Hprefactor Hinner) (le_refl (Cc*d^3)))
  have H2:=H1.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left HFd (Nat.cast_nonneg depth)) (le_refl (Ct*d^3))) (mul_nonneg hTemp hd.le)) (le_refl (Cc*d^3)))
  have Hd43 : d^4 ≤ d^3:=by
    have H:=mul_le_mul_of_nonneg_left hd1 (pow_nonneg hd.le 3)
    nlinarith only [H]
  have HterminalSmall:=mul_le_mul_of_nonneg_left Hd43 (mul_nonneg hTemp hCt)
  apply H2.trans
  change Temp*d*((depth:ℝ)*(defect*q/den+(Co/den+Cf+Cfr)*d^2)+Ct*d^3)+Cc*d^3 ≤ _
  have HX:=add_le_add HterminalSmall (le_refl
    (defect*(Temp*(depth:ℝ)/den)*q*d+(Temp*(depth:ℝ)*(Co/den+Cf+Cfr)+Cc)*d^3))
  convert HX using 1 <;> dsimp only [defect,b,den] <;> ring

end OAI.SKFluctuations.Cavity
