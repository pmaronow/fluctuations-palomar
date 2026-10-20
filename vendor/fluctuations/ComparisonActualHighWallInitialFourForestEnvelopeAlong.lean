module

public import ComparisonActualHighWallInitialFourSecondLowModulusAlong
public import ComparisonActualGeneralOtherSourceSavedProfileSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

theorem actual_high_wall_initial_full_B0_envelope_nonneg
    (degree : ℕ) (C CiU CiB CiM : Fin degree→ℝ) (Cf Cr E d N eta : ℝ)
    (hC : ∀a,0 ≤ C a) (hCiU : ∀a,0 ≤ CiU a)
    (hCiB : ∀a,0 ≤ CiB a) (hCiM : ∀a,0 ≤ CiM a)
    (hCf : 0 ≤ Cf) (hCr : 0 ≤ Cr)
    (hE : 0 ≤ E) (hd : 0 ≤ d) (hN : 0 ≤ N) :
    0 ≤ actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr E d N eta := by
  unfold actualHighWallInitialFullB0Envelope actualHighWallInitialLiveB0Envelope
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro a _
    have HU:=original_initial_low_moment_modulus_nonneg hE
      (mul_nonneg (hCiU a) hd) 8
    have HB:=original_initial_low_moment_modulus_nonneg hE
      (mul_nonneg (hCiB a) hd) 8
    have HM:=original_initial_low_moment_modulus_nonneg hE
      (mul_nonneg (hCiM a) hd) 4
    have HN:0 ≤ N^(-eta):=Real.rpow_nonneg hN _
    exact mul_nonneg (hC a) (by linarith only [HU,HB,HM,HN])
  · have HM:=original_initial_low_moment_modulus_nonneg hE
      (mul_nonneg hCr hd) (2*(degree+1))
    exact mul_nonneg hCf (add_nonneg (mul_nonneg hCr HM) (pow_nonneg hd _))

theorem actual_general_four_other_source_initial_forest_price
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as : List PositiveMass} {i star U : ℕ}
    (d qga qg qsite qsecond Di Dstar I : ℝ)
    (Cga Cg Cl Cj C4 CY Ch Cgl Cjl Cd C2 : ℝ)
    (f g : ℕ→ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    (hd : 0 ≤ d)
    (hA : 0 ≤ Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)
    (hB : 0 ≤ CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)
    (hP : 0 ≤ Cga+2*Cl+Cj+C4+CY) (hR : 0 ≤ Ch)
    (Hrow : ∀Q∈rows,
      |(d⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q| ≤
        |Q.term.coefficient| *d*
          (d^3*(Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)+
            d^2*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)+
            d*(Cga+2*Cl+Cj+C4+CY)*
              (Q.tree.forkCost f+edgeBudget 0 as f)+
            d^2*Ch*(Q.tree.forkCost g+edgeBudget 0 as g)))
    (Vcoef Vprofile Vradius : ℝ)
    (Hcoef : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ Vcoef)
    (Hprofile : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤ Vprofile)
    (Hradius : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost g+edgeBudget 0 as g))).sum ≤ Vradius) :
    |actualGeneralFourOtherSourceErrorSum bf hf U d rows| ≤
      d^4*(Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)*Vcoef+
      d^3*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)*Vcoef+
      d^2*(Cga+2*Cl+Cj+C4+CY)*Vprofile+
      d^3*Ch*Vradius := by
  let A:=Cga*qga+Cg*qg+Cd*qsite+C2*qsecond
  let B:=CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I
  let CP:=Cga+2*Cl+Cj+C4+CY
  let CR:=Ch
  let P (Q : NativeActualResourceState (Spin n×Bool) as i star):=
    Q.tree.forkCost f+edgeBudget 0 as f
  let R (Q : NativeActualResourceState (Spin n×Bool) as i star):=
    Q.tree.forkCost g+edgeBudget 0 as g
  have hbase:0 ≤ d^3*A+d^2*B:=
    add_nonneg (mul_nonneg (pow_nonneg hd _) hA) (mul_nonneg (pow_nonneg hd _) hB)
  have hCP:0 ≤ d*CP:=mul_nonneg hd hP
  have hCR:0 ≤ d^2*CR:=mul_nonneg (pow_nonneg hd _) hR
  have Hsum:
      (rows.map (fun Q=>|Q.term.coefficient| *d*
        (d^3*A+d^2*B+d*CP*(P Q)+d^2*CR*(R Q)))).sum=
      d*((d^3*A+d^2*B)*(rows.map (fun Q=>|Q.term.coefficient|)).sum+
        d*CP*(rows.map (fun Q=>|Q.term.coefficient| *(P Q))).sum+
        d^2*CR*(rows.map (fun Q=>|Q.term.coefficient| *(R Q))).sum) := by
    clear Hrow Hcoef Hprofile Hradius
    induction rows with
    | nil => simp
    | cons Q rows ih =>
        simp only [List.map_cons,List.sum_cons] at ih ⊢
        rw [ih]
        ring
  have Hraw:
      |actualGeneralFourOtherSourceErrorSum bf hf U d rows| ≤
        (rows.map (fun Q=>|Q.term.coefficient| *d*
          (d^3*A+d^2*B+d*CP*(P Q)+d^2*CR*(R Q)))).sum := by
    exact (native_abs_sum_map_le _ _).trans
      (List.sum_le_sum (by simpa only [A,B,CP,CR,P,R] using Hrow))
  have HC:=mul_le_mul_of_nonneg_left Hcoef hbase
  have HP:=mul_le_mul_of_nonneg_left Hprofile hCP
  have HR:=mul_le_mul_of_nonneg_left Hradius hCR
  calc
    _ ≤ (rows.map (fun Q=>|Q.term.coefficient| *d*
        (d^3*A+d^2*B+d*CP*(P Q)+d^2*CR*(R Q)))).sum:=Hraw
    _=d*((d^3*A+d^2*B)*(rows.map (fun Q=>|Q.term.coefficient|)).sum+
        d*CP*(rows.map (fun Q=>|Q.term.coefficient| *(P Q))).sum+
        d^2*CR*(rows.map (fun Q=>|Q.term.coefficient| *(R Q))).sum):=Hsum
    _ ≤ d*((d^3*A+d^2*B)*Vcoef+d*CP*Vprofile+d^2*CR*Vradius):=by
      apply mul_le_mul_of_nonneg_left _ hd
      linarith only [HC,HP,HR]
    _=d^4*A*Vcoef+d^3*B*Vcoef+d^2*CP*Vprofile+d^3*CR*Vradius:=by ring
    _=_:=by dsimp only [A,B,CP,CR]

theorem actual_general_four_other_source_initial_forest_split_profile_price
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as : List PositiveMass} {i star U : ℕ}
    (d qga qg qsite qsecond Di Dstar I : ℝ)
    (Cga Cg Cl Cj C4 CY Ch Cgl Cjl Cd C2 : ℝ)
    (f g : ℕ→ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    (hd : 0 ≤ d)
    (hA : 0 ≤ Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)
    (hB : 0 ≤ CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)
    (hP : 0 ≤ Cga+2*Cl+Cj+C4+CY) (hR : 0 ≤ Ch)
    (Hrow : ∀Q∈rows,
      |(d⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q| ≤
        |Q.term.coefficient| *d*
          (d^3*(Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)+
            d^2*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)+
            d*(Cga+2*Cl+Cj+C4+CY)*
              ((Q.tree.forkCost f+edgeBudget 0 as f)+
                d*(Q.tree.forkCost g+edgeBudget 0 as g))+
            d^2*Ch*(Q.tree.forkCost g+edgeBudget 0 as g)))
    (Vcoef Vprofile Vradius : ℝ)
    (Hcoef : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ Vcoef)
    (Hprofile : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤ Vprofile)
    (Hradius : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost g+edgeBudget 0 as g))).sum ≤ Vradius) :
    |actualGeneralFourOtherSourceErrorSum bf hf U d rows| ≤
      d^4*(Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)*Vcoef+
      d^3*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)*Vcoef+
      d^2*(Cga+2*Cl+Cj+C4+CY)*Vprofile+
      d^3*(Cga+2*Cl+Cj+C4+CY+Ch)*Vradius := by
  have Hrow' : ∀Q∈rows,
      |(d⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q| ≤
        |Q.term.coefficient| *d*
          (d^3*(Cga*qga+Cg*qg+Cd*qsite+C2*qsecond)+
            d^2*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)+
            d*(Cga+2*Cl+Cj+C4+CY)*(Q.tree.forkCost f+edgeBudget 0 as f)+
            d^2*(Cga+2*Cl+Cj+C4+CY+Ch)*
              (Q.tree.forkCost g+edgeBudget 0 as g)) := by
    intro Q hQ
    convert Hrow Q hQ using 1
    ring
  have hPR : 0 ≤ Cga+2*Cl+Cj+C4+CY+Ch:=by linarith only [hP,hR]
  exact actual_general_four_other_source_initial_forest_price bf hf
    d qga qg qsite qsecond Di Dstar I Cga Cg Cl Cj C4 CY
    (Cga+2*Cl+Cj+C4+CY+Ch) Cgl Cjl Cd C2 f g rows hd hA hB hP hPR
    Hrow' Vcoef Vprofile Vradius Hcoef Hprofile Hradius

theorem actual_general_four_initial_forest_radius_sum_le_combined_profile
    {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    (ho : MassOrdered 0 as) (d : ℝ)
    (f g : ℕ→ℝ) (hf : ∀j,0 ≤ f j)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    d*(rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost g+edgeBudget 0 as g))).sum ≤
      (rows.map (fun Q=>|Q.term.coefficient| *
        (Q.tree.forkCost (fun j=>f j+d*g j)+
          edgeBudget 0 as (fun j=>f j+d*g j)))).sum := by
  have Hrow (Q : NativeActualResourceState (Spin n×Bool) as i star) :
      d*(|Q.term.coefficient| *(Q.tree.forkCost g+edgeBudget 0 as g)) ≤
        |Q.term.coefficient| *
          (Q.tree.forkCost (fun j=>f j+d*g j)+
            edgeBudget 0 as (fun j=>f j+d*g j)) := by
    have HF : Q.tree.forkCost (fun j=>f j+d*g j)=
        Q.tree.forkCost f+d*Q.tree.forkCost g := by
      simpa only [one_mul] using (native_forkCost_test_linear Q.tree f g 1 d)
    have HE : edgeBudget 0 as (fun j=>f j+d*g j)=
        edgeBudget 0 as f+d*edgeBudget 0 as g := by
      simpa only [one_mul] using (native_edgeBudget_test_linear as 0 f g 1 d)
    rw [HF,HE]
    have HP : 0 ≤ Q.tree.forkCost f+edgeBudget 0 as f:=
      add_nonneg (Q.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
    have HH : |Q.term.coefficient| *(d*(Q.tree.forkCost g+edgeBudget 0 as g)) ≤
        |Q.term.coefficient| *
          ((Q.tree.forkCost f+edgeBudget 0 as f)+
            d*(Q.tree.forkCost g+edgeBudget 0 as g)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left HP) (abs_nonneg Q.term.coefficient)
    convert HH using 1 <;> ring
  have Hsum :
      d*(rows.map (fun Q=>|Q.term.coefficient| *
        (Q.tree.forkCost g+edgeBudget 0 as g))).sum =
      (rows.map (fun Q=>d*(|Q.term.coefficient| *
        (Q.tree.forkCost g+edgeBudget 0 as g)))).sum := by
    induction rows with
    | nil => simp
    | cons Q rows ih =>
        simp only [List.map_cons,List.sum_cons]
        rw [mul_add,ih]
  rw [Hsum]
  exact List.sum_le_sum (fun Q _=>Hrow Q)

theorem actual_general_four_initial_forest_power_sum_le_combined_profile
    {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    (ho : MassOrdered 0 as) (d : ℝ) (hd : 0 ≤ d)
    (f g : ℕ→ℝ) (hg : ∀j,0 ≤ g j)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      (rows.map (fun Q=>|Q.term.coefficient| *
        (Q.tree.forkCost (fun j=>f j+d*g j)+
          edgeBudget 0 as (fun j=>f j+d*g j)))).sum := by
  apply List.sum_le_sum
  intro Q _
  have HF : Q.tree.forkCost (fun j=>f j+d*g j)=
      Q.tree.forkCost f+d*Q.tree.forkCost g := by
    simpa only [one_mul] using (native_forkCost_test_linear Q.tree f g 1 d)
  have HE : edgeBudget 0 as (fun j=>f j+d*g j)=
      edgeBudget 0 as f+d*edgeBudget 0 as g := by
    simpa only [one_mul] using (native_edgeBudget_test_linear as 0 f g 1 d)
  rw [HF,HE]
  have HR : 0 ≤ Q.tree.forkCost g+edgeBudget 0 as g:=
    add_nonneg (Q.tree.forkCost_nonneg hg) (edgeBudget_nonneg ho hg)
  have HH : |Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f) ≤
      |Q.term.coefficient| *
        ((Q.tree.forkCost f+edgeBudget 0 as f)+
          d*(Q.tree.forkCost g+edgeBudget 0 as g)) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hd HR))
      (abs_nonneg Q.term.coefficient)
  convert HH using 1
  ring

theorem actual_high_wall_initial_four_centered_forest_modulus_price
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i star U depth degree : ℕ)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (C CiU CiB CiM : Fin degree→ℝ) (Cf Cr eta : ℝ)
    (qga qg qsite Di Dstar I : ℝ)
    (Cga Cg Cl Cj C4 CY Ch Cgl Cjl Cd : ℝ)
    (f g : ℕ→ℝ)
    (Vcoef Vprofile Vradius : ℝ)
    (hA : 0 ≤ Cga*qga+Cg*qg+Cd*qsite+
      2*actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
        (originalHighWallInitialPairErrorScale M as i) M.data.d (n:ℝ) eta)
    (hB : 0 ≤ CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)
    (hP : 0 ≤ Cga+2*Cl+Cj+C4+CY) (hR : 0 ≤ Ch)
    (Hrow : ∀Q∈actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
      [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))],
      |(M.data.d⁻¹)^Q.generation*
        actualGeneralFourOtherSourceErrorContrast M.bf M.hf U Q| ≤
        |Q.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 [.initial]*
          (M.data.d^3*(Cga*qga+Cg*qg+Cd*qsite+
              2*actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
                (originalHighWallInitialPairErrorScale M as i) M.data.d (n:ℝ) eta)+
            M.data.d^2*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)+
            M.data.d*(Cga+2*Cl+Cj+C4+CY)*
              ((Q.tree.forkCost f+edgeBudget 0 as f)+
                M.data.d*(Q.tree.forkCost g+edgeBudget 0 as g))+
            M.data.d^2*Ch*(Q.tree.forkCost g+edgeBudget 0 as g)))
    (Hcoef : ((actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
      [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))]).map
        (fun Q=>|Q.term.coefficient|)).sum ≤ Vcoef)
    (Hprofile : ((actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
      [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))]).map
        (fun Q=>|Q.term.coefficient| *
          (Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤ Vprofile)
    (Hradius : ((actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
      [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))]).map
        (fun Q=>|Q.term.coefficient| *
          (Q.tree.forkCost g+edgeBudget 0 as g))).sum ≤ Vradius) :
    |actualGeneralFourOtherSourceErrorSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
        [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))])| ≤
      M.data.d^4*(Cga*qga+Cg*qg+Cd*qsite+
        2*actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
          (originalHighWallInitialPairErrorScale M as i) M.data.d (n:ℝ) eta)*Vcoef+
      M.data.d^3*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)*Vcoef+
      M.data.d^2*(Cga+2*Cl+Cj+C4+CY)*Vprofile+
      M.data.d^3*(Cga+2*Cl+Cj+C4+CY+Ch)*Vradius := by
  have Hrow' : ∀Q∈actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
      [nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))],
      |(M.data.d⁻¹)^Q.generation*
        actualGeneralFourOtherSourceErrorContrast M.bf M.hf U Q| ≤
        |Q.term.coefficient| *M.data.d*
          (M.data.d^3*(Cga*qga+Cg*qg+Cd*qsite+
              2*actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
                (originalHighWallInitialPairErrorScale M as i) M.data.d (n:ℝ) eta)+
            M.data.d^2*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)+
            M.data.d*(Cga+2*Cl+Cj+C4+CY)*
              ((Q.tree.forkCost f+edgeBudget 0 as f)+
                M.data.d*(Q.tree.forkCost g+edgeBudget 0 as g))+
            M.data.d^2*Ch*(Q.tree.forkCost g+edgeBudget 0 as g)) := by
    simpa [nativeResourceScale,NativeResourceMark.savedScale] using Hrow
  simpa only [one_mul] using
    (actual_general_four_other_source_initial_forest_split_profile_price M.bf M.hf
    M.data.d qga qg qsite
    (2*actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
      (originalHighWallInitialPairErrorScale M as i) M.data.d (n:ℝ) eta)
    Di Dstar I Cga Cg Cl Cj C4 CY Ch Cgl Cjl Cd 1 f g _
    M.data.hd.le (by simpa only [one_mul] using hA) hB hP hR
    (by simpa only [one_mul] using Hrow') Vcoef Vprofile Vradius Hcoef Hprofile Hradius)

end OAI.SKFluctuations.Cavity
