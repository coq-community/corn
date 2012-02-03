Require Import
  List NPeano
  QArith Qabs Qpossec Qsums Qround
  Qmetric ZArith
  CRArith CRsum AbstractIntegration
  util.Qgcd
  Program
  uneven_CRplus
  stdlib_omissions.P
  stdlib_omissions.Z
  stdlib_omissions.Q.

Open Scope uc_scope.

Set Automatic Introduction.

Hint Resolve Qpos_nonzero.
Hint Immediate Q.Qle_nat.
Hint Resolve Qmult_le_0_compat.
Hint Resolve QnonNeg.Qplus_nonneg.

Parameter (z:Z).

(* Zsqrt_plain_is_pos *)

(*
Lemma Zsqrt_r_nonneg (z: Z) (E: 0 <= z): (0 <= Zsqrt z)%Z.
Proof with auto.
  destruct Zsqrt; try easy.
  admit.
 subst. simpl. omega.
Qed.
*)

Require Import Coq.ZArith.Zsqrt_compat.

Open Scope Z_scope.

Definition Z_4th_root_floor (x: Z): (0 <= x)%Z ->
  {s: Z & {r: Z | x = Zpower s 4 + r /\ Zpower s 4 <= x < Zpower (s + 1) 4}}%Z.
Proof.
 intro E.
 destruct x.
   exists 0%Z.
   exists 0%Z.
   split. reflexivity.
   change (0 <= 0 < 1).
   omega.
  exists (projT1 (Zsqrt (projT1 (Zsqrt p (Zle_0_pos p))) (Zsqrt_plain_is_pos p E))).
  set (Zsqrt (projT1 (Zsqrt p (Zle_0_pos p))) (Zsqrt_plain_is_pos p E)).
  admit.
 exfalso. apply E. reflexivity.
Defined.

Definition Z_4th_root_floor_plain (z: Z): Z :=
  match z with
  | Zpos p => projT1 (Z_4th_root_floor p (Zle_0_pos p))
  | _ => 0%Z
  end.

Lemma Zle_uniq {x y: Z} (p q: Zle x y): p = q.
Admitted.

Goal forall z, Z_4th_root_floor_plain z = Zsqrt_plain (Zsqrt_plain z).
Proof.
 intros.
 unfold Zsqrt_plain.
 destruct z; try reflexivity.
 unfold Z_4th_root_floor_plain, Z_4th_root_floor.
 unfold projT1 at 1.
 generalize (Zsqrt_plain_is_pos). (* p (Zle_0_pos p)). *)
 unfold Zsqrt_plain.
 generalize (Zsqrt). (*p (Zle_0_pos p)).*)
 admit.
(*
 destruct s.
 simpl @projT1 at 1.
 destruct x.
   simpl. reflexivity. *)
admit.
admit.
(* 
rewrite (Zle_uniq z (Zle_0_pos p)).
   intro.
  reflexivity.
 simpl. intro. exfalso. apply z. reflexivity.*)
Qed.

Definition Q_4th_root_floor_plain (q: Q): Z := Z_4th_root_floor_plain (Qceiling q).

Section definition.

  Context 
    (f: Q_as_MetricSpace --> CR)
    (b: Q). (* bound for the absolute value of f's fourth derivative *)

  Section approx.

    Context (fr: Q) (w: Qpos) (e: Qpos).

    Definition N: positive := P_of_succ_nat (Zabs_nat (Q_4th_root_floor_plain ((w^5) / 2880 * b / e))).
      (* This Zabs is silly because we know the squaring thing only returns nonnegatives, but whatever. *)
      (* Also, a ceil variant would obviate need to take the successor, but I haven't defined ceil variants
       of the 4th root for Z/Q yet. *)

    Definition iw: Qpos := (w / N)%Qpos.
    Definition halfiw: Qpos := (w / ((2#1) * N))%Qpos.
Open Scope Q_scope.
    Definition simpson (fr: Q): CR :=
      (' (iw / 6) * (f fr + f (fr + halfiw)%Q * '4 + f (fr + iw)%Q))%CR.

    Definition approx: CR := CRsum_list (map (fun i: nat => simpson (fr + i * iw)) (N.enum (nat_of_P N))).

  End approx.

  Lemma regular fr w: is_RegularFunction_noInf CR (approx fr w).
  Admitted.
Print mkRegularFunction.
  Definition simpson_integral fr w: CR := Cjoin (mkRegularFunction ('(0%Q))%CR (regular fr w)).

(*
  Global Instance integrate: Integral f := @integral_extended_to_nn_width f pre_result.
*)

End definition.

(*
Open Scope Q_scope.

Definition answer (n:positive) (r:CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.


Require Import CRsin.

Print simpson_integral.

Time Eval compute in (answer 3 (simpson_integral sin_uc 1 0 1)).
(*
     = 459
     : Z
Finished transaction in 17. secs (16.597038u,0.064004s)
*)

*)