(** * Write a CoRN sparse-raster as PPM file (portable pix map) *)

(* The conversion from a sparse-raster to a 2D list of bools is done as Coq program. *)
(* The output of the Pixmap to a file in PPM is done as Elpi program
   (Elpi is correctly the only tactic language which allows to write files) *)

From CoRN Require Import Plot RasterQ Qmetric.

Require Import ZArith.
Require Import Orders.
Require Import Mergesort.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Import elpi.elpi.

(** A module for sorting the points of the sparse raster first by y and then by x coordinate *)

Module SparseRasterOrder <: TotalLeBool.
  Definition t := (Z*Z)%type.
  Definition leb (x y : t) :=
    let (x1,x2):=x in
    let (y1,y2):=y in
    Z.ltb x1 y1 || (Z.eqb x1 y1) && (Z.leb x2 y2).
  Theorem leb_total : forall x y : t, (eq (leb x y) true) \/ (eq (leb y x) true).
  Proof.
    intros x y.
    unfold leb.
    destruct x as [x1 x2], y as [y1 y2].
    lia. (* I love lia so much! *)
  Qed.
End SparseRasterOrder.

Module Import SparseRasterSort := Sort SparseRasterOrder.

(* The function sorts a list of (x,y) pairs first be y and then by x coordinate *)

Local Example SparseRasterSort'Ex1: eq 
  (SparseRasterSort.sort [(2, 1); (2, 2); (0, 2); (0, 1); (1, 1); (1, 0)]%Z)
  [(0, 1); (0, 2); (1, 0); (1, 1); (2, 1); (2, 2)]%Z.
Proof. reflexivity. Qed.

Fixpoint sparseRasterSorted_getLine (data : list (Z*Z)) (row : Z) : (list Z) * (list (Z*Z)) :=
  match data with
  | [] => ([], [])
  | (y,x)::t =>
    if Z.eqb y row
    then let (current,rest) := sparseRasterSorted_getLine t row in (x::current, rest)
    else ([],data)
  end.

(* If row matches the y coordinate of the first element, the function returns the 
   list of the x coordinates of the leading elements with this y coordinate and the remaining (x,y) pairs *)

Local Example sparseRasterSorted_getLine'Ex1: eq 
  (sparseRasterSorted_getLine [(0, 1); (0, 2); (1, 0); (1, 1); (2, 1); (2, 2)]%Z 0)
  ([1; 2]%Z, [(1, 0); (1, 1); (2, 1); (2, 2)]%Z).
Proof. reflexivity. Qed.

(* Otherwise the x coordinate list is empty and the (x,y) pair list is returned unaltered *)

Local Example sparseRasterSorted_getLine'Ex2: eq 
  (sparseRasterSorted_getLine [(0, 1); (0, 2); (1, 0); (1, 1); (2, 1); (2, 2)]%Z 1)
  ([], [(0, 1); (0, 2); (1, 0); (1, 1); (2, 1); (2, 2)]%Z).
Proof. reflexivity. Qed.

Definition listSorted_removeDuplicates {T : Type} (eqb : T->T->bool) (data : list T) :=
  let fix aux (data : list T) :=
    match data with
    | [] => data
    | [a] => data
    | a::(b::t) as t'=> if eqb a b then aux t' else a::(aux t')
    end
  in aux data.

Local Example listSorted_removeDuplicates'Ex1: eq (listSorted_removeDuplicates Z.eqb [1;2;2;3;3;3]%Z) [1;2;3]%Z.
Proof. reflexivity. Qed. 

Definition sparseRasterLine_rasterize (width : positive) (row : list Z) : list bool :=
  let fix aux (width : nat) (x : Z) (row : list Z) : list bool :=
    match width, row with
    | O, _ => []
    | S w', [] => false :: (aux w' 0%Z row)
    | S w', h::t => if Z.eqb h x then true :: (aux w' (x+1)%Z t) else false :: (aux w' (x+1)%Z row)
    end
  in aux (Pos.to_nat width) 0%Z (listSorted_removeDuplicates Z.eqb row).

Local Example sparseRasterLine_rasterize'Ex1: eq 
  (sparseRasterLine_rasterize 10%positive [2;4;4;5]%Z)
  [false; false; true; false; true; true; false; false; false; false].
Proof. reflexivity. Qed.

Definition sparseRaster_rasterize {width height : positive} (sr : sparse_raster width height)
: positive * positive * list (list bool)
:=
  let '(sparse_raster_data _ _ data) := sr in
  let data_sorted := SparseRasterSort.sort data in
  let fix aux (nrows : nat) (irow : Z) (rest : list (Z*Z)) :=
    match nrows with
    | O => []
    | S nrows' =>
      let (row, rest') := sparseRasterSorted_getLine rest irow in
      let rownd := listSorted_removeDuplicates Z.eqb row in
      sparseRasterLine_rasterize width row :: aux nrows' (irow+1)%Z rest'
    end in
  (width, height, aux (Pos.to_nat height) 0%Z data_sorted).

Local Example sparseRaster_rasterize'Ex1 : eq 
  (sparseRaster_rasterize (sparse_raster_data 3 4 [(3, 1); (3, 2); (0, 2); (0, 1); (1, 1); (1, 0)]%Z))
  (3%positive, 4%positive, [ 
    [false; true;  true ]; 
    [true;  true;  false];
    [false; false; false];
    [false; true;  true ]
  ] ).
Proof. reflexivity. Qed.

Elpi Command WritePPM.
Elpi Accumulate lp:{{

  % Convert a Coq positive to an ELpi int
  pred coq-pos->elpi-int i:term, o:int.
  coq-pos->elpi-int {{ xH }} 1 :- !.
  coq-pos->elpi-int {{ xO lp:X }} Y :- calc (2 * { coq-pos->elpi-int X} ) Y, !.
  coq-pos->elpi-int {{ xI lp:X }} Y :- calc (2 * { coq-pos->elpi-int X} + 1) Y, !.
  coq-pos->elpi-int T I :- coq.say "coq-pos->elpi-int: Unexpected term" T I, !.

  % Convert a CoRN "sparse_raster" to a 2D Coq list of booleans
  pred sparse-raster-rasterize i:term, o:int, o:int, o:term.
  sparse-raster-rasterize DC NRE NCE DCR :-
    coq.reduction.vm.norm {{ sparseRaster_rasterize lp:DC }} _ {{ (lp:NRC, lp:NCC, lp:DCR) }},
    coq-pos->elpi-int NRC NRE,
    coq-pos->elpi-int NCC NCE, !.
  sparse-raster-rasterize T _ _ _ :- coq.say "sparse-raster-rasterize: Unexpected term" T, !.

  % Convert a Coq list of booleans to an Elpi 01 string with "\n" termination
  pred raster-row-to-string i:term, o:string.
  raster-row-to-string {{ [] }} "\n".
  raster-row-to-string {{ false :: lp:T }} S :- raster-row-to-string T TS, calc ("0" ^ TS) S.
  raster-row-to-string {{ true :: lp:T }} S :- raster-row-to-string T TS, calc ("1" ^ TS) S.
  raster-row-to-string T _ :- coq.say "raster-row-to-string: Unexpected term" T.

  % Write a Coq 2D list of booleans as lines of 01 data to an output stream
  pred raster-write-rows i:out_stream, i:term.
  raster-write-rows _ {{ [] }}.
  raster-write-rows OS {{ lp:ROW :: lp:T }} :-
    raster-row-to-string ROW ROWS,
    output OS ROWS,
    raster-write-rows OS T.

  % Main function of command
  main [str FILEPATH, trm PM] :-
    sparse-raster-rasterize PM PMNR PMNC PMData,
    % Write PPM header
    open_out FILEPATH OSTREAM,
    output OSTREAM "P1\n",
    output OSTREAM { calc (int_to_string PMNR) },
    output OSTREAM " ",
    output OSTREAM { calc (int_to_string PMNC) },
    output OSTREAM "\n",
    % Write PPM data
    raster-write-rows OSTREAM PMData,
    close_out OSTREAM
  .
}}.
Elpi Typecheck.

