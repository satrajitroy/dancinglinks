(******************************************************************************
 * GDance.v
 *
 * A purely functional Rocq/Coq implementation of Knuth's generalized
 * Dancing Links idea (gdance):
 *
 *   - primary items are exact-cover obligations;
 *   - uncolored items are covered in the ordinary Algorithm X sense;
 *   - colored items are purified: rows with incompatible colors are removed,
 *     rows with the same color may coexist;
 *   - backtracking is ordinary structural recursion over immutable problems,
 *     so there is no explicit uncover/unpurify operation.
 *
 * This file intentionally keeps gdance-flavored names such as cover, purify,
 * choose_col, commit, search, and solve, while avoiding pointers, gotos,
 * global arrays, and destructive circular lists.
 ******************************************************************************/

From Coq Require Import List Bool Arith String.
Import ListNotations.
Open Scope string_scope.

Module GDance.

Set Implicit Arguments.

(******************************************************************************)
(* Basic decidable equality layer                                               *)
(******************************************************************************)

Class Eqb (A : Type) := {
  eqb : A -> A -> bool
}.

Arguments eqb {A} {_} _ _.

Class EqbLaws (A : Type) `{Eqb A} := {
  eqb_true_iff : forall x y : A, eqb x y = true <-> x = y
}.

Global Instance Eqb_nat : Eqb nat := {
  eqb := Nat.eqb
}.

Global Instance EqbLaws_nat : EqbLaws nat.
Proof.
  constructor.
  intros x y.
  apply Nat.eqb_eq.
Qed.

Global Instance Eqb_string : Eqb string := {
  eqb := String.eqb
}.

Global Instance EqbLaws_string : EqbLaws string.
Proof.
  constructor.
  intros x y.
  apply String.eqb_eq.
Qed.

(******************************************************************************)
(* Core data model                                                              *)
(******************************************************************************)

Record citem (Item Color : Type) := CItem {
  ci_col   : Item;
  ci_color : option Color
}.

Arguments CItem {Item Color} _ _.
Arguments ci_col {Item Color} _.
Arguments ci_color {Item Color} _.

Record row (Item Color RowId : Type) := Row {
  row_id    : RowId;
  row_items : list (citem Item Color)
}.

Arguments Row {Item Color RowId} _ _.
Arguments row_id {Item Color RowId} _.
Arguments row_items {Item Color RowId} _.

Record problem (Item Color RowId : Type) := Problem {
  primary_items : list Item;
  rows          : list (row Item Color RowId)
}.

Arguments Problem {Item Color RowId} _ _.
Arguments primary_items {Item Color RowId} _.
Arguments rows {Item Color RowId} _.

(******************************************************************************)
(* Functional generalized Dancing Links                                         *)
(******************************************************************************)

Section FunctionalGDance.

Context {Item Color RowId : Type}.
Context `{Eqb Item}.
Context `{Eqb Color}.
Context `{Eqb RowId}.

Definition row_eqb (r s : row Item Color RowId) : bool :=
  eqb (row_id r) (row_id s).

Definition remove_primary (i : Item) (ps : list Item) : list Item :=
  filter (fun j => negb (eqb j i)) ps.

Definition cell_on (i : Item) (r : row Item Color RowId) : option (citem Item Color) :=
  find (fun ci => eqb (ci_col ci) i) (row_items r).

Definition row_has_col (i : Item) (r : row Item Color RowId) : bool :=
  match cell_on i r with
  | Some _ => true
  | None => false
  end.

Definition rows_with_col
  (i : Item)
  (rs : list (row Item Color RowId))
  : list (row Item Color RowId) :=
  filter (row_has_col i) rs.

Definition col_len (i : Item) (p : problem Item Color RowId) : nat :=
  length (rows_with_col i (rows p)).

(*
   In gdance terms:

     cover c

   removes c from the active primary header list if c is primary, and removes
   all active rows that mention c.  For secondary/unlisted items, the primary
   list is unchanged, but rows mentioning c are still removed.
*)
Definition cover (i : Item) (p : problem Item Color RowId) : problem Item Color RowId :=
  Problem
    (remove_primary i (primary_items p))
    (filter (fun r => negb (row_has_col i r)) (rows p)).

(*
   Two colored entries are compatible exactly when both are colored and their
   colors are equal.  If either occurrence is uncolored, sharing the column is
   an exact-cover conflict.
*)
Definition colors_compatible (x y : option Color) : bool :=
  match x, y with
  | Some a, Some b => eqb a b
  | _, _ => false
  end.

Definition conflict_on_col
  (a b : citem Item Color)
  : bool :=
  if eqb (ci_col a) (ci_col b)
  then negb (colors_compatible (ci_color a) (ci_color b))
  else false.

Definition conflicts_with
  (r s : row Item Color RowId)
  : bool :=
  existsb
    (fun a => existsb (fun b => conflict_on_col a b) (row_items s))
    (row_items r).

Definition compatible_rows
  (r s : row Item Color RowId)
  : bool :=
  negb (conflicts_with r s).

(*
   A row is compatible with a purification of item i to color x if either it
   does not mention i, or it mentions i with exactly color x.  Mentioning i
   uncolored, or with a different color, is incompatible.
*)
Definition row_color_ok
  (i : Item)
  (x : Color)
  (r : row Item Color RowId)
  : bool :=
  match cell_on i r with
  | None => true
  | Some ci =>
      match ci_color ci with
      | Some y => eqb y x
      | None => false
      end
  end.

(*
   Functional counterpart of gdance's purify.  It does not remove a primary
   obligation; it only filters active rows by color compatibility for i.
*)
Definition purify
  (i : Item)
  (x : Color)
  (p : problem Item Color RowId)
  : problem Item Color RowId :=
  Problem
    (primary_items p)
    (filter (row_color_ok i x) (rows p)).

Definition commit_cell
  (ci : citem Item Color)
  (p : problem Item Color RowId)
  : problem Item Color RowId :=
  match ci_color ci with
  | None => cover (ci_col ci) p
  | Some x => purify (ci_col ci) x p
  end.

Definition commit_other_cell
  (chosen_col : Item)
  (ci : citem Item Color)
  (p : problem Item Color RowId)
  : problem Item Color RowId :=
  if eqb (ci_col ci) chosen_col
  then p
  else commit_cell ci p.

(*
   Commit a chosen row from a chosen primary column:

     1. cover the chosen primary column;
     2. for every other item in the chosen row:
          - cover it if uncolored;
          - purify it if colored.

   This is the immutable analogue of gdance's destructive sequence.  There is
   no recover/uncover phase because the caller retains the old problem value.
*)
Definition commit
  (chosen_col : Item)
  (chosen_row : row Item Color RowId)
  (p : problem Item Color RowId)
  : problem Item Color RowId :=
  fold_left
    (fun acc ci => commit_other_cell chosen_col ci acc)
    (row_items chosen_row)
    (cover chosen_col p).

(*
   This compressed form is sometimes useful for proofs/debugging.  It is not
   used by search below, because commit is closer to gdance's cover/purify
   decomposition.
*)
Definition remove_conflicting_rows
  (chosen : row Item Color RowId)
  (rs : list (row Item Color RowId))
  : list (row Item Color RowId) :=
  filter
    (fun r => negb (orb (row_eqb chosen r) (conflicts_with chosen r)))
    rs.

Fixpoint choose_col_aux
  (p : problem Item Color RowId)
  (best : Item)
  (best_len : nat)
  (rest : list Item)
  : Item :=
  match rest with
  | [] => best
  | i :: rest' =>
      let n := col_len i p in
      if Nat.ltb n best_len
      then choose_col_aux p i n rest'
      else choose_col_aux p best best_len rest'
  end.

Definition choose_col (p : problem Item Color RowId) : option Item :=
  match primary_items p with
  | [] => None
  | i :: rest => Some (choose_col_aux p i (col_len i p) rest)
  end.

Fixpoint search
  (fuel : nat)
  (p : problem Item Color RowId)
  : list (list (row Item Color RowId)) :=
  match fuel with
  | O => []
  | S fuel' =>
      match primary_items p with
      | [] => [[]]
      | _ =>
          match choose_col p with
          | None => [[]]
          | Some c =>
              flat_map
                (fun r =>
                   map
                     (fun sol => r :: sol)
                     (search fuel' (commit c r p)))
                (rows_with_col c (rows p))
          end
      end
  end.

Definition solve := search.

Definition solution_row_ids
  (sol : list (row Item Color RowId))
  : list RowId :=
  map row_id sol.

Definition solve_ids
  (fuel : nat)
  (p : problem Item Color RowId)
  : list (list RowId) :=
  map solution_row_ids (solve fuel p).

(******************************************************************************)
(* Specification predicates / proof hooks                                       *)
(******************************************************************************)

Definition rows_from_problem
  (p : problem Item Color RowId)
  (sol : list (row Item Color RowId))
  : Prop :=
  Forall (fun r => In r (rows p)) sol.

Definition primary_exactly_once
  (p : problem Item Color RowId)
  (sol : list (row Item Color RowId))
  : Prop :=
  forall i,
    In i (primary_items p) ->
    exists r,
      In r sol /\
      row_has_col i r = true /\
      forall r',
        In r' sol ->
        row_has_col i r' = true ->
        r' = r.

Definition rows_pairwise_compatible
  (sol : list (row Item Color RowId))
  : Prop :=
  forall r s,
    In r sol ->
    In s sol ->
    r <> s ->
    conflicts_with r s = false.

Definition valid_solution
  (p : problem Item Color RowId)
  (sol : list (row Item Color RowId))
  : Prop :=
  rows_from_problem p sol /\
  primary_exactly_once p sol /\
  rows_pairwise_compatible sol.

Definition row_columns
  (r : row Item Color RowId)
  : list Item :=
  map ci_col (row_items r).

Definition row_no_duplicate_columns
  (r : row Item Color RowId)
  : Prop :=
  NoDup (row_columns r).

Definition rows_have_unique_ids
  (rs : list (row Item Color RowId))
  : Prop :=
  NoDup (map row_id rs).

Definition primary_items_uncolored
  (p : problem Item Color RowId)
  : Prop :=
  forall r ci,
    In r (rows p) ->
    In ci (row_items r) ->
    In (ci_col ci) (primary_items p) ->
    ci_color ci = None.

Definition problem_wf
  (p : problem Item Color RowId)
  : Prop :=
  NoDup (primary_items p) /\
  Forall row_no_duplicate_columns (rows p) /\
  rows_have_unique_ids (rows p) /\
  primary_items_uncolored p.

(*
   A good eventual theorem target for this file:

     Theorem solve_sound :
       forall fuel p sol,
         problem_wf p ->
         In sol (solve fuel p) ->
         valid_solution p sol.

   The implementation above is intentionally proof-oriented, but this file does
   not admit or assert the theorem.  It leaves the soundness proof to a separate
   proof file or later section.
*)

End FunctionalGDance.

(******************************************************************************)
(* Small executable examples                                                    *)
(******************************************************************************)

Module Examples.

Definition I := string.
Definition C := nat.
Definition R := nat.

Definition u (i : I) : citem I C := CItem i None.
Definition k (i : I) (c : C) : citem I C := CItem i (Some c).

(*
   Primaries: A, B
   Secondary colored item: X

   Rows 1 and 2 share X with the same color and therefore may coexist.
   Row 3 shares X with a different color and is incompatible with either.
*)
Definition r1 : row I C R := Row 1 [u "A"; k "X" 7].
Definition r2 : row I C R := Row 2 [u "B"; k "X" 7].
Definition r3 : row I C R := Row 3 [u "B"; k "X" 9].

Definition demo_problem : problem I C R :=
  Problem ["A"; "B"] [r1; r2; r3].

Definition demo_solutions : list (list R) :=
  solve_ids 5 demo_problem.

(* Expected shape: [[1; 2]], up to row ordering determined by choose_col/search. *)

End Examples.

End GDance.
