Require Import
  List NPeano
  QArith Qabs Qpossec Qsums Qround
  Qmetric ZArith
  CRArith CRsum (*AbstractIntegration*)
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
 (*generalize (Zsqrt).*) (*p (Zle_0_pos p)).*)
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

    Context (n : positive)(fr: Q) (w: Qpos) (e: Qpos).

    Definition N: positive := P_of_succ_nat (Zabs_nat (Q_4th_root_floor_plain ((w^5) / 2880 * b / e))).
      (* This Zabs is silly because we know the squaring thing only returns nonnegatives, but whatever. *)
      (* Also, a ceil variant would obviate need to take the successor, but I haven't defined ceil variants
       of the 4th root for Z/Q yet. *)

    Definition iw : Qpos := (w / N)%Qpos.
    Definition iw1 : Qpos := (w / n)%Qpos.
    Definition halfiw : Qpos := (w / ((2#1) * N))%Qpos.
    Definition halfiw1 : Qpos := (w / ((2#1) * n))%Qpos.

    Open Scope Q_scope.

    Definition simpson (fr: Q): CR :=
      (' (iw / 6) * (f fr + f (fr + halfiw)%Q * '4 + f (fr + iw)%Q))%CR.
    Definition simpson1 (fr: Q): CR :=
      (' (iw1) * (f fr + f (fr + halfiw1)%Q * '4 + f (fr + iw1)%Q))%CR.

    Definition approx: CR := CRsum_list (map (fun i: nat => simpson (fr + i * iw)) (N.enum (nat_of_P N))).
    Definition approx1 : CR :=
      CRsum_list (map (fun i: nat => simpson1 (fr + i * iw1)) (N.enum (nat_of_P n))).

  End approx.

  Lemma regular fr w: is_RegularFunction_noInf CR (approx fr w).
  Admitted.

  Definition simpson_integral fr w: CR := Cjoin (mkRegularFunction ('(0%Q))%CR (regular fr w)).

(*
  Global Instance integrate: Integral f := @integral_extended_to_nn_width f pre_result.
*)

End definition.

Require Import ARtrans.
Require Import Qdlog.
Require Import BigQ ARbigQ ARQ ARbigD.

Definition eps (n : positive) := (1 # (10^n))%Qpos.

Definition answer (n:positive) (r:CR) : Z :=
 let m := (10^n)%positive in
 let (a,b) := ((approximate r (1#m)%Qpos) * m)%Q in
 Zdiv a b.


(*Time Eval vm_compute in approximate (simpson_integral sin_uc 1 0 1) (1#100000)%Qpos.*)

Definition sum_pos `{Zero A, Plus A} (f : positive -> A) (n : positive) :=
  Pos.peano_rect (λ _, A) 0 (λ p x, f p + x) n.

Definition sum_pos_iter `{Zero A, Plus A} (f : positive -> A) (n : positive) : A :=
match n with
| xH => 0
| _ =>
  let z :=
    Pos.iter
      (Pos.pred n)
      (λ y : positive * A, let (p, x) := y in ((Pos.succ p), (f p + x)))
      (1%positive, 0) in
    snd z
end.

Section ARsum.

Context `{AppRationals AQ}.

Definition ARsum_list_raw (l : list AR) (e : QposInf) : AQ :=
fold_left (@plus AQ _)
match l with
| nil => nil
| cons h t =>
  let e' := QposInf_mult (1#(Pos.of_nat (length t)))%Qpos e in
   (map (fun x => approximate x e') l)
end
0.

Definition ARsum_raw (f : positive -> AR) (n : positive) (eps : QposInf) : AQ :=
let e := (eps * (1 # Pos.pred n)%Qpos)%QposInf in
  sum_pos_iter (λ p, approximate (f p) e) n.

Lemma ARsum_list_prf : forall l, @is_RegularFunction AQ_as_MetricSpace (ARsum_list_raw l).
Admitted.

Lemma ARsum_prf : forall f n, @is_RegularFunction AQ_as_MetricSpace (ARsum_raw f n).
Admitted.

Definition ARsum_list (l : list AR) : AR := Build_RegularFunction (ARsum_list_prf l).

Definition ARsum (f : positive -> AR) (n : positive) : AR := Build_RegularFunction (ARsum_prf f n).

End ARsum.

Section ARInt.

Context
  `{AppRationals AQ}
  (f : AR -> AR)
  (B : Q) (* bound for the absolute value of f's fourth derivative *)
  (a b : AR) (w : AQ).

Let width : AR := b - a.

Section ARIntN.

Variable n : positive.

Section ARIntEps.

Variable eps : Qpos.

Let hl' : AR := width * AQinv ('(Zpos n~0)). (* hl' = width / (2 * n) *)
Let eps' : Qpos := eps * (1 # (6 * n)%positive)%Qpos.
Let h (p : positive) := approximate (f (a + ARscale ('(Zpos p)) hl')) eps'.

Definition ARsimpson_sum_raw : AQ :=
  4 * (sum_pos_iter (λ p, h (Pos.pred_double p)) (Pos.succ n)) +
  2 * (sum_pos_iter (λ p, h p~0) n) +
  (approximate (f a) eps' + approximate (f b) eps').

End ARIntEps.

Lemma ARsimson_sum_regular : is_RegularFunction_noInf AQ_as_MetricSpace ARsimpson_sum_raw.
Admitted.

Definition ARsimpson_sum : AR := mkRegularFunction 0 ARsimson_sum_regular.

End ARIntN.

Section ARIntEps1.

Variable eps : Qpos.

Definition num_intervals : nat := S (Z.to_nat (Q_4th_root_floor_plain ('w^5 / 2880 * B / eps))).
(* To be optimized *)
Definition num_intervals1 : positive :=
  P_of_succ_nat (Zabs_nat (Q_4th_root_floor_plain (('w^5) / 2880 * B / eps))). 

Definition num_intervals2 : positive :=
  let w : Q := 'approximate width (1#1000)%Qpos + (1#1000) in
    Pos.succ (Z.to_pos (Q_4th_root_floor_plain (w^5 / 2880 * B / eps))).

(* half-length *)
Let hl : AR := width * AQinv ('(Zpos (num_intervals2~0)%positive)).

Let f' (n : nat) := f(a + '(n : Z) * 'w * AQinv ('(2 * (num_intervals : Z))%Z)).
Let g (p : positive) := f(a + ARscale ('(Zpos p)) hl).
(*Let h (p : positive) (e : Qpos) := approximate (f (a + ARscale ('(Zpos p)) hl)) e.*)

Definition ARsimpson_raw : AR :=
  (ARscale 4 (ARsum_list (map (fun i : nat => f' (2 * i + 1)) (N.enum (num_intervals - 0)))) +
   ARscale 2 (ARsum_list (map (fun i : nat => f' (2 * i + 2)) (N.enum (num_intervals - 1)))) +
   (f' 0 + f' (2 * num_intervals))) * 'w * AQinv ('(6 * (num_intervals : Z))%Z).

Definition ARsimpson1_raw : AR :=
  ((ARscale 4 (ARsum (λ p, g (Pos.pred_double p)) (Pos.succ num_intervals2))) +
   (ARscale 2 (ARsum (λ p, g p~0) num_intervals2)) +
   (f a + f b))
  * width * AQinv ('(6 * (num_intervals2 : Z))%Z).

(*Definition ARsimpson_sum_raw : AQ :=
  let e := eps * (1 # (6 * num_intervals2)%positive)%Qpos in
    4 * (sum_pos_iter (λ p, h (Pos.pred_double p) e) (Pos.succ num_intervals2)) +
    2 * (sum_pos_iter (λ p, h p~0 e) num_intervals2) +
    (approximate (f a) e + approximate (f b) e).*)

Definition ARsimpson2_raw : AR :=
  ARsimpson_sum num_intervals2 * (width * AQinv ('Zpos (6 * num_intervals2)%positive)).

End ARIntEps1.

Lemma ARsimson_regular : is_RegularFunction_noInf AR ARsimpson_raw.
Admitted.

Lemma ARsimson1_regular : is_RegularFunction_noInf AR ARsimpson1_raw.
Admitted.

Lemma ARsimson2_regular : is_RegularFunction_noInf AR ARsimpson2_raw.
Admitted.

Definition ARsimpson : AR := Cjoin (mkRegularFunction 0 ARsimson_regular).
Definition ARsimpson1 : AR := Cjoin (mkRegularFunction 0 ARsimson1_regular).
Definition ARsimpson2 : AR := Cjoin (mkRegularFunction 0 ARsimson2_regular).

End ARInt.

(*Time Compute approximate (ARexp (AQ := bigD) 4) (eps 2000)

Time Check approximate ((ARexp (AQ := bigD) 4) * '((10 ^ 1000)%positive : Z)) (1#1)%Qpos.*)

(*Compute N 3 1 (eps 20).
Compute num_intervals (AQ := bigD) 3 1 (eps 13).*)

(*Extraction "mult.ml" ARmult.*)

(*Time Compute approximate (simpson_integral (exp_bound_uc 2) 3 0 1) (eps 11).*)

(*
(* The following shows that in evaluating x * y up to eps, (approximate x
(eps / (2 * c))) where c is an approximation of y up to 1, is computed once
and not twice. We make y very large so that the approximation of x takes a
long time. Multiplcation takes less than twice the time of the approximation of x. *)

Definition int := (ARsimpson (AQ := bigD) (ARexp_bounded (AQ := bigD) 2) 3 0 1).
Definition e := '((10 ^ 12)%positive : Z) : ARbigD.

Time Compute approximate (int * e) (1#1)%Qpos.

Time Compute approximate int (eps 13).
*)

(* (ARexp x) calls ARexp_bounded on (Qceiling ('approximate x (1#1)%Qpos + (1#1))) and x.
If x = 1, then the approximation is 2. *)

Definition repeat {A : Type} (M : unit -> A) (n : positive) :=
  Pos.iter n (fun _ => (fun _ => tt) (M tt)) tt.

(*Definition M :=
  fun _ : unit =>
    approximate (ARexp_bounded (AQ := bigD) 2 1) (eps 12).*)

(*Compute num_intervals2 (AQ := bigD) 3 0 1 (eps 15).*)

(*Time Compute approximate (ARsimpson (AQ := bigD) (ARexp_bounded (AQ := bigD) 2) 3 0 1) (eps 14).
Time Compute approximate (ARsimpson1 (AQ := bigD) (ARexp_bounded (AQ := bigD) 2) 3 0 1) (eps 14).*)
(*Time Compute approximate (ARsimpson2 (AQ := Q) (ARexp_bounded 2) 3 0 1) (eps 9).
Time Compute approximate (ARsimpson_sum (AQ := bigD) (ARexp_bounded (AQ := bigD) 2) 0 1 1012) (eps 14).*)

Section Picard.

Context `{AppRationals AQ} (F : AR -> AR) (a b : AR).

Definition picard (f : AR -> AR) (x : AR) := b + ARsimpson2 (AQ := AQ) (λ t, F (f t)) 1 a x.

Definition picard_iter (n : nat) : AR -> AR := nat_iter n picard (λ _, b).

End Picard.

Definition d := approximate (picard_iter (AQ := bigD) (λ y, y) 0 1 6 1) (eps 1).

Extraction "simpson.ml" d.

Time Compute approximate (picard_iter (AQ := bigD) (λ y, y) 0 1 6 1) (eps 1).




(*Time Compute approximate (ARsimpson (AQ := bigD) ARexp 3 0 1) (eps 10).
Time Compute approximate (ARsimpson (AQ := bigD) ARarctan 1 0 1) (eps 1).
Time Compute approximate (ARsimpson (AQ := bigD) ARsqrt 3 0 1) (eps 12).
Timeout 30 Compute approximate (ARsimpson (AQ := bigD) ARexp 3 0 1) (eps 1).
Compute num_intervals (AQ := bigD) 3 1 (eps 0).*)

Section ARInt'.

Context
  `{AppRationals AQ}
  (f : AQ -> AR)
  (B : Q). (* bound for the absolute value of f's fourth derivative *)

Section ARapprox.

  Context (n : positive) (a : AQ) (w : AQ) (eps : Qpos).

  Definition N' : nat := Z.to_nat (1 + Zdiv (Qdlog2 ('w^5 / 2880 * B / eps))%Q 4).

  Definition iw' : AQ := w ≪ -(N' : Z).
  Definition iw1' : AQ := w ≪ -(n : Z).

  Definition simpson' (a' : AQ) : AR :=
    ('iw' * (f a' + f (a' + (iw' ≪ -1)) * '4 + f (a' + iw'))).
  Definition simpson1' (a' : AQ) : AR :=
    ('iw1' * (f a' + f (a' + (iw1' ≪ -1)) * '4 + f (a' + iw1'))).

  Definition approx' : AR :=
    ARsum_list (map (fun i : nat => simpson' (a + '(i : Z) * iw')) (N.enum (2^N'))).
  Definition approx1' : AR :=
    ARsum_list (map (fun i : nat => simpson1' (a + '(i : Z) * iw1')) (N.enum (nat_of_P (2^n)%positive))).

End ARapprox.

Lemma regular' a w : is_RegularFunction_noInf AR (approx' a w).
Admitted.

Definition simpson_integral' a w : AR := Cjoin (mkRegularFunction 0 (regular' a w)).

End ARInt'.

Time Compute approximate (simpson_integral' (AQ := bigD) AQexp 3 0 1) (eps 10).
Time Compute approximate (simpson_integral' (AQ := bigD) ARexp 3 0 1) (eps 10).


(*Eval compute in N' (AQ := bigD) 1 1 (eps 8).
Eval compute in N 1 1 (eps 8).*)

(*Time Check approximate (ARexp_bounded_uc (AQ := bigD) 2 1) (eps 20).
Time Check approximate (ARexp (AQ := bigD) 1) (eps 20).

Time Eval vm_compute in approximate (ARexp_bounded_uc (AQ := bigD) 2 1) (eps 20).
Time Eval vm_compute in approximate (ARexp (AQ := bigD) 1) (eps 20).*)

(*Time Check approximate (Cjoin_fun (Cmap_fun AQPrelengthSpace (ARexp_bounded_uc (AQ := bigD) 2) 1)) (eps 20).
Time Eval vm_compute in
  approximate (Cjoin_fun (Cmap_fun AQPrelengthSpace (ARexp_bounded_uc (AQ := bigD) 2) 1)) (eps 20).*)

Time Eval vm_compute in approximate (ARexp (AQ := bigD) 1) (eps 20).
Time Eval vm_compute in approximate (exp 1) (eps 20).
Time Eval vm_compute in approximate (exp_bound_uc 3 1) (eps 130).

Time Eval vm_compute in approximate (ARsin_uc (AQ := bigD) 1) (eps 20).
Time Eval vm_compute in approximate (sin_uc 1) (eps 20).

Time Eval vm_compute in approximate (sin_slow 1) (eps 50).
Time Eval vm_compute in approximate (ARsin (AQ := bigD) 1) (eps 50).

Require Import PowerSeries.

Time Eval vm_compute in
  approximate (ARsin (AQ := bigD) (ARsin (AQ := bigD) (ARsin (AQ := bigD) 1))) (eps 25).

Time Eval vm_compute in approximate (approx1 sin_uc 32 0 1) (eps 50).
Time Eval vm_compute in approximate (approx1' (AQ := bigD) ARsin_uc 5 0 1) (eps 50).



Time Eval vm_compute in
  (fun _ => tt) (map (fun _ => approximate (ARsin_uc (AQ := bigD) 1) (eps 10)) (N.enum 10)).
Time Eval vm_compute in
  (fun _ => tt) (map (fun _ => approximate (sin_uc 1) (eps 10)) (N.enum 10)).


Time Eval vm_compute in approximate (approx' (AQ := bigD) ARsin_uc 1 0 1 (eps 8)) (eps 8).

Time Eval vm_compute in approximate (simpson_integral sin_uc 1 0 1) (1#100000000)%Qpos.
Time Eval vm_compute in answer 8 (simpson_integral sin_uc 1 0 1).

(*Eval vm_compute in approximate (simpson' (AQ := bigD) ARsin_uc 1 1 (1#1)%Qpos 0) (1#1)%Qpos.*)

(*Eval vm_compute in (*cast _ Q*)
  (approximate (approx' (AQ := bigD) ARsin_uc 1 0 1 (1#10)%Qpos) (1#10)%Qpos).*)


Time Eval vm_compute in
  cast _ Q (approximate (simpson_integral' (AQ := bigD) ARsin_uc 1 0 1) (1#100000000)%Qpos).

Time Eval vm_compute in N.enum ((2 : nat)^(N' (AQ := bigD) 1 1 (1#10000000000)%Qpos)).
