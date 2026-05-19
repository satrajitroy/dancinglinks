(** * GDance : Verified Functional Dancing Links with Colored Constraints

    GDance is a functional Rocq formalization of the generalized/colored
    Dancing Links solver developed in this repository's [gdance.c].

    The underlying algorithmic idea is Knuth-style Algorithm X / Dancing Links:
    primary items are exact-cover obligations, secondary items are optional
    constraints, and colored secondary items are handled by purification.  The
    Rocq development preserves the terminology and structure used by [gdance.c],
    including names such as [cover], [purify], [choose_col], [commit], [search],
    and [solve].

    The port is intentionally close to the original [gdance.c] design, but the
    representation is changed to suit proof and extraction:

    - C pointers, mutable circular lists, global arrays, and destructive updates
      are replaced by immutable records and lists;
    - destructive cover/uncover and purify/unpurify operations are replaced by
      construction of residual problems;
    - backtracking is expressed as structurally recursive search with an
      explicit fuel parameter.

    The development is organized into four layers:

    - a small generic data model for rows, columns, colored items, and problems;
    - a purely functional solver based on [cover], [purify], [commit], and
      recursive search;
    - a soundness proof showing that every returned solution is valid for a
      well-formed problem;
    - public problem-generator APIs for Sudoku-like problems, warehouse and
      scheduling-style problems, combinatorics, N-Queens, Langford pairs, and
      van der Waerden-style generated colorings.

    The extracted OCaml/Melange/JavaScript artifact powers a browser demo.
    Large examples may exceed browser recursion or memory limits; those are
    JavaScript runtime limits, not claims about the mathematical solver
    specification.

    The main exported guarantee is:

    [[
      solve_sound :
        forall fuel p sol,
          problem_wf p ->
          In sol (solve fuel p) ->
          valid_solution p sol
    ]]

    Informally: every solution returned by [solve] is composed of problem rows,
    covers each primary item exactly once, and satisfies pairwise colored
    compatibility.

    This is a partial-correctness result.  Completeness and fuel adequacy are
    separate properties and are not claimed by [solve_sound].
*)

From Stdlib Require Import List Bool Arith String.
Import ListNotations.
Open Scope string_scope.

Module Core.

  Set Implicit Arguments.

      (** ** Boolean equality and equality laws

        The solver is polymorphic in the types of item columns, colors, and row
        identifiers.  Instead of requiring decidable equality from the standard
        library directly, the executable code uses a small [Eqb] class.

        The proof layer assumes [EqbLaws], which connects executable boolean
        equality to propositional equality:

        [[
          eqb x y = true <-> x = y
        ]]

        This separation keeps the extracted solver simple while giving the proof
        scripts enough logical strength to reason about equality soundly.
    *)

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

    Global Instance EqbLaws_nat : EqbLaws.
    Proof.
      constructor.
      intros x y.
      apply Nat.eqb_eq.
    Qed.

    Global Instance Eqb_string : Eqb string := {
      eqb := String.eqb
    }.

    Global Instance EqbLaws_string : EqbLaws.
    Proof.
      constructor.
      intros x y.
      apply String.eqb_eq.
    Qed.

    (** ** Core data model

        A [citem] is a column occurrence inside a row.

        - [ci_col] is the logical column.
        - [ci_color] is [None] for an ordinary/uncolored occurrence.
        - [ci_color = Some c] represents a colored occurrence.

        A [row] has a row identifier and a list of [citem]s.

        A [problem] consists of:

        - [primary_items], which must be covered exactly once by a solution;
        - [rows], the candidate rows available to the solver.

        Columns that appear in rows but are not listed in [primary_items] behave as
        secondary constraints.  Uncolored secondary columns conflict if shared.
        Colored secondary columns may coexist only when their colors are compatible.
    *)

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

    (** ** Functional Algorithm X / Core solver

        This section contains the executable solver.

        The implementation follows the spirit of Knuth's Dancing Links algorithm,
        but uses immutable lists and structural recursion rather than pointers and
        mutation.

        The key operations are:

        - [cover], which removes a primary/uncolored column from the remaining
          problem;
        - [purify], which keeps only rows compatible with a chosen colored column;
        - [commit], which applies the consequences of choosing one row;
        - [choose_col], which chooses the next primary column to branch on;
        - [search], which recursively enumerates solutions subject to a fuel bound;
        - [solve], the public solver over rows;
        - [solve_ids], a convenience wrapper returning row identifiers.

        The [fuel] parameter is an explicit termination bound.  Soundness does not
        require fuel adequacy: any solution returned within the given fuel is valid.
        Completeness requires a separate fuel-adequacy theorem and is intentionally
        not claimed here.
    *)

    Context {Item Color RowId : Type}.
    Context `{Eqb Item}.
    Context `{Eqb Color}.
    Context `{Eqb RowId}.

    Notation CItemT := (citem Item Color).
    Notation RowT := (row Item Color RowId).
    Notation ProblemT := (problem Item Color RowId).

    Section Code.

      (** *** Executable definitions

          The definitions in this subsection are computational and survive extraction.
          Proofs and propositions in later subsections are erased by extraction.
      *)

      (* begin hide *)


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
        List.length (rows_with_col i (rows p)).

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

      (* end hide *)

    End Code.

    (******************************************************************************)
    (* Specification predicates / proof hooks                                       *)
    (******************************************************************************)

    Section Proofs.

      (** ** Problem well-formedness and solution validity

          The solver is proved sound for well-formed problems.

          The well-formedness predicate records the assumptions under which the
          generic solver behaves as intended.  In particular, generated Sudoku,
          warehouse, and combinatorics APIs are expected to produce problems satisfying
          these invariants.

          A [valid_solution] consists of three semantic properties:

          - every selected row comes from the original problem;
          - every primary item is covered exactly once;
          - selected rows are pairwise compatible, including colored secondary
            compatibility.

          This predicate is the mathematical specification used by [solve_sound].
      *)

      (* begin hide *)

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

      (** ** Soundness proof structure

          The soundness proof is organized around the behavior of [commit].

          The central characterization lemma is [row_survives_commit_iff], which
          describes exactly which rows survive after a chosen row is committed.

          From that characterization we derive:

          - [commit_preserves_wf], showing that recursive calls remain
            well-formed;
          - [commit_survivors_compatible], showing that surviving rows do not
            conflict with the chosen row;
          - [commit_extends_primary], showing that primary exactness lifts
            from the recursive subproblem back to the original problem;
          - [commit_extends_solution], combining row membership, primary coverage, and
            compatibility.

          These lemmas feed the main theorem [solve_sound].
      *)

      Lemma empty_solution_valid_when_no_primaries :
        forall (p : problem Item Color RowId),
          problem_wf p ->
          primary_items p = [] ->
          valid_solution p [].
      Proof.
        intros p Hwf Hprim.
        unfold valid_solution.
        split.
        - unfold rows_from_problem.
          constructor.
        - split.
          + unfold primary_exactly_once.
            intros i Hi.
            rewrite Hprim in Hi.
            contradiction.
          + unfold rows_pairwise_compatible.
            intros r s Hr Hs Hneq.
            contradiction.
      Qed.

      Lemma NoDup_filter_bool :
        forall (A : Type) (P : A -> bool) (xs : list A),
          NoDup xs ->
          NoDup (filter P xs).
      Proof.
        intros A P xs.
        induction xs as [|x xs IH]; intros Hnd; simpl.
        - constructor.
        - inversion Hnd as [|? ? Hnotin Hnodup]; subst.
          destruct (P x) eqn:HP; simpl.
          + constructor.
            * intro Hin.
              apply filter_In in Hin as [Hin _].
              apply Hnotin.
              exact Hin.
            * apply IH.
              exact Hnodup.
          + apply IH.
            exact Hnodup.
      Qed.

      Lemma Forall_filter_rows :
        forall (P : row Item Color RowId -> bool) rs,
          Forall row_no_duplicate_columns rs ->
          Forall row_no_duplicate_columns (filter P rs).
      Proof.
        intros P rs HForall.
        apply Forall_forall.
        intros r Hr.
        apply filter_In in Hr as [Hr _].
        rewrite Forall_forall in HForall.
        apply HForall.
        exact Hr.
      Qed.

      Lemma rows_have_unique_ids_filter :
        forall (P : row Item Color RowId -> bool) rs,
          rows_have_unique_ids rs ->
          rows_have_unique_ids (filter P rs).
      Proof.
        intros P rs.
        unfold rows_have_unique_ids.
        induction rs as [|r rs IH]; intros Hnd; simpl in *.
        - constructor.
        - inversion Hnd as [|? ? Hnotin Hnodup]; subst.
          destruct (P r) eqn:HP; simpl.
          + constructor.
            * intro Hin.
              apply in_map_iff in Hin.
              destruct Hin as [r' [Hid Hr']].
              apply filter_In in Hr' as [Hr' _].
              apply Hnotin.
              apply in_map_iff.
              exists r'.
              split.
              -- exact Hid.
              -- exact Hr'.
            * apply IH.
              exact Hnodup.
          + apply IH.
            exact Hnodup.
      Qed.

      Lemma cover_preserves_problem_wf :
        forall (p : problem Item Color RowId) i,
          problem_wf p ->
          problem_wf (cover i p).
      Proof.
        intros p i Hwf.
        destruct Hwf as [Hprim [Hrows [Hids Huncolored]]].
        unfold cover.
        simpl.
        repeat split.
        - apply NoDup_filter_bool.
          exact Hprim.
        - apply Forall_filter_rows.
          exact Hrows.
        - apply rows_have_unique_ids_filter.
          exact Hids.
        - unfold primary_items_uncolored in *.
          intros r ci Hr Hci Hi.
          apply filter_In in Hr as [Hr _].
          apply filter_In in Hi as [Hi _].
          eapply Huncolored; eauto.
      Qed.

      Lemma purify_preserves_problem_wf :
        forall (p : problem Item Color RowId) i x,
          problem_wf p ->
          problem_wf (purify i x p).
      Proof.
        intros p i x Hwf.
        destruct Hwf as [Hprim [Hrows [Hids Huncolored]]].
        unfold purify.
        simpl.
        repeat split.
        - exact Hprim.
        - apply Forall_filter_rows.
          exact Hrows.
        - apply rows_have_unique_ids_filter.
          exact Hids.
        - unfold primary_items_uncolored in *.
          intros r ci Hr Hci Hi.
          apply filter_In in Hr as [Hr _].
          eapply Huncolored; eauto.
      Qed.

      Lemma commit_cell_preserves_problem_wf :
        forall (ci : citem Item Color) p,
          problem_wf p ->
          problem_wf (commit_cell ci p).
      Proof.
        intros ci p Hwf.
        unfold commit_cell.
        destruct (ci_color ci) as [x|].
        - apply purify_preserves_problem_wf.
          exact Hwf.
        - apply cover_preserves_problem_wf.
          exact Hwf.
      Qed.

      Lemma commit_other_cell_preserves_problem_wf :
        forall chosen_col (ci : citem Item Color) p,
          problem_wf p ->
          problem_wf (commit_other_cell chosen_col ci p).
      Proof.
        intros chosen_col ci p Hwf.
        unfold commit_other_cell.
        destruct (eqb (ci_col ci) chosen_col) eqn:Heq.
        - exact Hwf.
        - apply commit_cell_preserves_problem_wf.
          exact Hwf.
      Qed.

      Lemma fold_commit_other_cell_preserves_problem_wf :
        forall chosen_col cis p,
          problem_wf p ->
          problem_wf
            (fold_left
              (fun acc ci => commit_other_cell chosen_col ci acc)
              cis
              p).
      Proof.
        intros chosen_col cis.
        induction cis as [|ci cis IH]; intros p Hwf; simpl.
        - exact Hwf.
        - apply IH.
          apply commit_other_cell_preserves_problem_wf.
          exact Hwf.
      Qed.

      Lemma commit_preserves_wf :
        forall (p : problem Item Color RowId) best r,
          problem_wf p ->
          In r (rows_with_col best (rows p)) ->
          problem_wf (commit best r p).
      Proof.
        intros p best r Hwf Hr.
        unfold commit.
        apply fold_commit_other_cell_preserves_problem_wf.
        apply cover_preserves_problem_wf.
        exact Hwf.
      Qed.

      Lemma rows_with_col_in_rows :
        forall i rs r,
          In r (rows_with_col i rs) ->
          In r rs.
      Proof.
        intros i rs r Hr.
        unfold rows_with_col in Hr.
        apply filter_In in Hr.
        exact (proj1 Hr).
      Qed.

      Lemma cover_rows_subset :
        forall (p : problem Item Color RowId) i r',
          In r' (rows (cover i p)) ->
          In r' (rows p).
      Proof.
        intros p i r' Hin.
        unfold cover in Hin.
        simpl in Hin.
        apply filter_In in Hin as [Hin _].
        exact Hin.
      Qed.

      Lemma purify_rows_subset :
        forall (p : problem Item Color RowId) i x r',
          In r' (rows (purify i x p)) ->
          In r' (rows p).
      Proof.
        intros p i x r' Hin.
        unfold purify in Hin.
        simpl in Hin.
        apply filter_In in Hin as [Hin _].
        exact Hin.
      Qed.

      Lemma commit_cell_rows_subset :
        forall (ci : citem Item Color) p r',
          In r' (rows (commit_cell ci p)) ->
          In r' (rows p).
      Proof.
        intros ci p r' Hin.
        unfold commit_cell in Hin.
        destruct (ci_color ci) as [x|] eqn:Hcolor.
        - eapply purify_rows_subset.
          exact Hin.
        - eapply cover_rows_subset.
          exact Hin.
      Qed.

      Lemma commit_other_cell_rows_subset :
        forall chosen_col (ci : citem Item Color) p r',
          In r' (rows (commit_other_cell chosen_col ci p)) ->
          In r' (rows p).
      Proof.
        intros chosen_col ci p r' Hin.
        unfold commit_other_cell in Hin.
        destruct (eqb (ci_col ci) chosen_col) eqn:Heq.
        - exact Hin.
        - eapply commit_cell_rows_subset.
          exact Hin.
      Qed.

      Lemma fold_commit_other_cell_rows_subset :
        forall chosen_col cis (p : problem Item Color RowId) r',
          In r'
            (rows
              (fold_left
                  (fun acc ci => commit_other_cell chosen_col ci acc)
                  cis
                  p)) ->
          In r' (rows p).
      Proof.
        intros chosen_col cis.
        induction cis as [|ci cis IH]; intros p r' Hin; simpl in Hin.
        - exact Hin.
        - specialize (IH (commit_other_cell chosen_col ci p) r' Hin) as Hmid.
          eapply commit_other_cell_rows_subset.
          exact Hmid.
      Qed.

      Lemma commit_rows_subset :
        forall (p : problem Item Color RowId) best r r',
          In r' (rows (commit best r p)) ->
          In r' (rows p).
      Proof.
        intros p best r r' Hin.
        unfold commit in Hin.
        apply cover_rows_subset with (i := best).
        eapply fold_commit_other_cell_rows_subset.
        exact Hin.
      Qed.

      Lemma bool_eq_by_true_iff :
        forall b1 b2 : bool,
          (b1 = true <-> b2 = true) ->
          b1 = b2.
      Proof.
        intros b1 b2 Hiff.
        destruct b1, b2; try reflexivity.
        - destruct Hiff as [Hforward _].
          specialize (Hforward eq_refl).
          discriminate.
        - destruct Hiff as [_ Hback].
          specialize (Hback eq_refl).
          discriminate.
      Qed.

      Context (Item_eqb_laws : @EqbLaws Item H).
      Context (Color_eqb_laws : @EqbLaws Color H0).

      Lemma eqb_sym_explicit :
        forall {A : Type} (EA : Eqb A) (L : @EqbLaws A EA) (x y : A),
          @eqb A EA x y = @eqb A EA y x.
      Proof.
        intros A EA L x y.
        destruct (@eqb A EA x y) eqn:Hxy.
        - apply (@eqb_true_iff A EA L) in Hxy.
          subst y.
          symmetry.
          apply (@eqb_true_iff A EA L).
          reflexivity.
        - destruct (@eqb A EA y x) eqn:Hyx.
          + apply (@eqb_true_iff A EA L) in Hyx.
            subst y.
            assert (@eqb A EA x x = true) as Hxx.
            {
              apply (@eqb_true_iff A EA L).
              reflexivity.
            }
            rewrite Hxx in Hxy.
            discriminate.
          + reflexivity.
      Qed.

      Lemma colors_compatible_symmetric :
        forall x y : option Color,
          colors_compatible x y = colors_compatible y x.
      Proof.
        intros x y.
        destruct x as [a|], y as [b|]; simpl; try reflexivity.
        apply (@eqb_sym_explicit Color H0 Color_eqb_laws).
      Qed.

      Lemma conflict_on_col_symmetric :
        forall a b : citem Item Color,
          conflict_on_col a b = conflict_on_col b a.
      Proof.
        intros a b.
        unfold conflict_on_col.

        rewrite (@eqb_sym_explicit Item H Item_eqb_laws
                  (ci_col a) (ci_col b)).

        destruct (eqb (ci_col b) (ci_col a)) eqn:Hcol.
        - rewrite colors_compatible_symmetric.
          reflexivity.
        - reflexivity.
      Qed.

      Lemma conflicts_with_symmetric :
        forall (r s : row Item Color RowId),
          conflicts_with r s = conflicts_with s r.
      Proof.
        intros r s.
        unfold conflicts_with.
        apply bool_eq_by_true_iff.
        split; intro Hin.
        - apply existsb_exists in Hin.
          destruct Hin as [a [Ha Hin_b]].
          apply existsb_exists in Hin_b.
          destruct Hin_b as [b [Hb Hconf]].

          apply existsb_exists.
          exists b.
          split.
          + exact Hb.
          + apply existsb_exists.
            exists a.
            split.
            * exact Ha.
            * rewrite <- conflict_on_col_symmetric.
              exact Hconf.

        - apply existsb_exists in Hin.
          destruct Hin as [b [Hb Hin_a]].
          apply existsb_exists in Hin_a.
          destruct Hin_a as [a [Ha Hconf]].

          apply existsb_exists.
          exists a.
          split.
          + exact Ha.
          + apply existsb_exists.
            exists b.
            split.
            * exact Hb.
            * rewrite conflict_on_col_symmetric.
              exact Hconf.
      Qed.

      Lemma eqb_true_eq_Item :
        forall x y : Item,
          eqb x y = true -> x = y.
      Proof.
        intros x y Hxy.
        apply (@eqb_true_iff Item H Item_eqb_laws x y).
        exact Hxy.
      Qed.

      Lemma eqb_false_neq_Item :
        forall x y : Item,
          eqb x y = false -> x <> y.
      Proof.
        intros x y Hxy Heq.
        subst y.
        assert (eqb x x = true) as Hxx.
        {
          apply (@eqb_true_iff Item H Item_eqb_laws x x).
          reflexivity.
        }
        rewrite Hxx in Hxy.
        discriminate.
      Qed.

      Lemma cover_rows_characterization :
        forall (p : problem Item Color RowId) i r',
          In r' (rows (cover i p)) <->
          In r' (rows p) /\ row_has_col i r' = false.
      Proof.
        intros p i r'.
        unfold cover.
        simpl.
        rewrite filter_In.
        rewrite negb_true_iff.
        reflexivity.
      Qed.

      Lemma purify_rows_characterization :
        forall (p : problem Item Color RowId) i x r',
          In r' (rows (purify i x p)) <->
          In r' (rows p) /\ row_color_ok i x r' = true.
      Proof.
        intros p i x r'.
        unfold purify.
        simpl.
        rewrite filter_In.
        reflexivity.
      Qed.

      Lemma commit_other_cell_rows_characterization :
        forall best (ci : citem Item Color) (p : problem Item Color RowId) r',
          In r' (rows (commit_other_cell best ci p)) <->
          In r' (rows p) /\
          (ci_col ci <> best ->
            match ci_color ci with
            | None =>
                row_has_col (ci_col ci) r' = false
            | Some x =>
                row_color_ok (ci_col ci) x r' = true
            end).
      Proof.
        intros best ci p r'.
        unfold commit_other_cell.
        destruct (eqb (ci_col ci) best) eqn:Heq.
        - split.
          + intro Hin.
            split.
            * exact Hin.
            * intro Hneq.
              exfalso.
              apply Hneq.
              apply eqb_true_eq_Item.
              exact Heq.
          + intros [Hin _].
            exact Hin.

        - assert (Hneq : ci_col ci <> best).
          {
            apply eqb_false_neq_Item.
            exact Heq.
          }

          unfold commit_cell.
          destruct (ci_color ci) as [x|] eqn:Hcolor.
          + rewrite purify_rows_characterization.
            split.
            * intros [Hin Hok].
              split.
              -- exact Hin.
              -- intro.  exact Hok.
            * intros [Hin Hcond].
              split.
              -- exact Hin.
              -- apply Hcond. exact Hneq.

          + rewrite cover_rows_characterization.
            split.
            * intros [Hin Hnot].
              split.
              -- exact Hin.
              -- intro. exact Hnot.
            * intros [Hin Hcond].
              split.
              -- exact Hin.
              -- apply Hcond. exact Hneq.
      Qed.

      Lemma fold_commit_other_cell_rows_characterization :
        forall best cis (p : problem Item Color RowId) r',
          In r'
            (rows
              (fold_left
                  (fun acc ci => commit_other_cell best ci acc)
                  cis
                  p)) <->
          In r' (rows p) /\
          forall ci,
            In ci cis ->
            ci_col ci <> best ->
            match ci_color ci with
            | None =>
                row_has_col (ci_col ci) r' = false
            | Some x =>
                row_color_ok (ci_col ci) x r' = true
            end.
      Proof.
        intros best cis.
        induction cis as [|ci cis IH]; intros p r'; simpl.
        - split.
          + intro Hin.
            split.
            * exact Hin.
            * intros ci Hci _.
              contradiction.
          + intros [Hin _].
            exact Hin.

        - rewrite IH.
          rewrite commit_other_cell_rows_characterization.
          split.
          + intros [[Hin Hci] Hrest].
            split.
            * exact Hin.
            * intros ci0 Hci0 Hneq0.
              destruct Hci0 as [Hsame | Hin_tail].
              -- subst ci0.
                apply Hci.
                exact Hneq0.
              -- apply Hrest.
                ++ exact Hin_tail.
                ++ exact Hneq0.

          + intros [Hin Hall].
            split.
            * split.
              -- exact Hin.
              -- intros Hneq.
                apply Hall.
                ++ left. reflexivity.
                ++ exact Hneq.
            * intros ci0 Hin_tail Hneq0.
              apply Hall.
              -- right. exact Hin_tail.
              -- exact Hneq0.
      Qed.

      Lemma row_survives_commit_iff :
        forall p best r r',
          In r' (rows (commit best r p)) <->
          In r' (rows p) /\
          row_has_col best r' = false /\
          forall ci,
            In ci (row_items r) ->
            ci_col ci <> best ->
            match ci_color ci with
            | None =>
                row_has_col (ci_col ci) r' = false
            | Some x =>
                row_color_ok (ci_col ci) x r' = true
            end.
      Proof.
        intros p best r r'.
        unfold commit.
        rewrite fold_commit_other_cell_rows_characterization.
        rewrite cover_rows_characterization.
        split.
        - intros [[Hin Hbest] Hall].
          split.
          + exact Hin.
          + split.
            * exact Hbest.
            * exact Hall.
        - intros [Hin [Hbest Hall]].
          split.
          + split.
            * exact Hin.
            * exact Hbest.
          + exact Hall.
      Qed.

      Lemma eqb_refl_Item :
        forall x : Item,
          eqb x x = true.
      Proof.
        intro x.
        apply (@eqb_true_iff Item H Item_eqb_laws x x).
        reflexivity.
      Qed.

      Lemma rows_with_col_has_col :
        forall i rs r,
          In r (rows_with_col i rs) ->
          row_has_col i r = true.
      Proof.
        intros i rs r Hr.
        unfold rows_with_col in Hr.
        apply filter_In in Hr.
        exact (proj2 Hr).
      Qed.

      Lemma row_has_col_of_in :
        forall i (r : row Item Color RowId) ci,
          In ci (row_items r) ->
          eqb (ci_col ci) i = true ->
          row_has_col i r = true.
      Proof.
        intros i r ci Hin Heq.
        unfold row_has_col, cell_on.
        induction (row_items r) as [|a rest IH]; simpl in *.
        - contradiction.
        - destruct Hin as [Ha | Hin].
          + subst a.
            rewrite Heq.
            reflexivity.
          + destruct (eqb (ci_col a) i) eqn:Ha.
            * reflexivity.
            * apply IH.
              exact Hin.
      Qed.

      Lemma row_has_col_false_no_cell :
        forall i (r : row Item Color RowId) ci,
          row_has_col i r = false ->
          In ci (row_items r) ->
          eqb i (ci_col ci) = false.
      Proof.
        intros i r ci Hfalse Hin.
        destruct (eqb i (ci_col ci)) eqn:Heq; auto.

        assert (Hsym : eqb (ci_col ci) i = true).
        {
          rewrite (@eqb_sym_explicit Item H Item_eqb_laws (ci_col ci) i).
          exact Heq.
        }

        assert (Hhas : row_has_col i r = true).
        {
          eapply row_has_col_of_in.
          - exact Hin.
          - exact Hsym.
        }

        rewrite Hfalse in Hhas.
        discriminate.
      Qed.

      Lemma eqb_false_of_neq_Item :
        forall x y : Item,
          x <> y ->
          eqb x y = false.
      Proof.
        intros x y Hneq.
        destruct (eqb x y) eqn:Hxy.
        - apply (@eqb_true_iff Item H Item_eqb_laws) in Hxy.
          contradiction.
        - reflexivity.
      Qed.

      Lemma row_no_duplicate_columns_from_problem_wf :
        forall (p : problem Item Color RowId) r,
          problem_wf p ->
          In r (rows p) ->
          row_no_duplicate_columns r.
      Proof.
        intros p r Hwf Hr.
        destruct Hwf as [_ [Hrows _]].
        rewrite Forall_forall in Hrows.
        apply Hrows.
        exact Hr.
      Qed.

      Lemma cell_on_some_in_match :
        forall i (r : row Item Color RowId) ci,
          cell_on i r = Some ci ->
          In ci (row_items r) /\ eqb (ci_col ci) i = true.
      Proof.
        intros i r ci Hcell.
        unfold cell_on in Hcell.
        apply find_some in Hcell.
        exact Hcell.
      Qed.

      Lemma cell_on_unique_no_dup :
        forall (r : row Item Color RowId) i ci,
          row_no_duplicate_columns r ->
          In ci (row_items r) ->
          eqb (ci_col ci) i = true ->
          cell_on i r = Some ci.
      Proof.
        intros r i ci Hnd Hin Heq.
        unfold row_no_duplicate_columns, row_columns in Hnd.
        unfold cell_on.

        induction (row_items r) as [|a rest IH]; simpl in *.
        - contradiction.
        - inversion Hnd as [|x xs Hnotin Hnd_tail]; subst.
          destruct Hin as [Ha | Hin].
          + subst a.
            rewrite Heq.
            reflexivity.
          + destruct (eqb (ci_col a) i) eqn:Ha_eq.
            * exfalso.
              apply Hnotin.

              apply (@eqb_true_iff Item H Item_eqb_laws) in Ha_eq.
              apply (@eqb_true_iff Item H Item_eqb_laws) in Heq.

              subst i.
              rewrite Ha_eq.
              apply in_map.
              exact Hin.

            * apply IH.
              -- exact Hnd_tail.
              -- exact Hin.
      Qed.

      Lemma row_color_ok_same_col_compatible :
        forall (r : row Item Color RowId) i x ci,
          row_no_duplicate_columns r ->
          In ci (row_items r) ->
          eqb i (ci_col ci) = true ->
          row_color_ok i x r = true ->
          colors_compatible (Some x) (ci_color ci) = true.
      Proof.
        intros r i x ci Hnd Hin Heq Hok.

        assert (Heq' : eqb (ci_col ci) i = true).
        {
          rewrite (@eqb_sym_explicit Item H Item_eqb_laws (ci_col ci) i).
          exact Heq.
        }

        unfold row_color_ok in Hok.

        assert (Hcell : cell_on i r = Some ci).
        {
          eapply cell_on_unique_no_dup; eauto.
        }

        rewrite Hcell in Hok.

        destruct (ci_color ci) as [y|] eqn:Hcolor; simpl in *.
        - rewrite (@eqb_sym_explicit Color H0 Color_eqb_laws x y).
          exact Hok.
        - discriminate.
      Qed.

      Lemma commit_survivors_compatible :
        forall (p : problem Item Color RowId) best r r',
          problem_wf p ->
          In r (rows_with_col best (rows p)) ->
          In r' (rows (commit best r p)) ->
          conflicts_with r r' = false.
      Proof.
        intros p best r r' Hwf Hr Hsurv.

        destruct (conflicts_with r r') eqn:Hconf.
        - exfalso.
          unfold conflicts_with in Hconf.

          apply existsb_exists in Hconf.
          destruct Hconf as [ci [Hci Hinner]].

          apply existsb_exists in Hinner.
          destruct Hinner as [dj [Hdj Hconf]].

          apply row_survives_commit_iff in Hsurv.
          destruct Hsurv as [Hr'_p [Hbest_not Hsurv_cells]].

          unfold conflict_on_col in Hconf.
          destruct (eqb (ci_col ci) (ci_col dj)) eqn:Hsame; try discriminate.

          destruct (eqb (ci_col ci) best) eqn:Hci_best.
          + apply (@eqb_true_iff Item H Item_eqb_laws) in Hci_best.
            subst best.

            assert (Hdj_has : row_has_col (ci_col ci) r' = true).
            {
              eapply row_has_col_of_in.
              - exact Hdj.
              - rewrite (@eqb_sym_explicit Item H Item_eqb_laws
                          (ci_col dj) (ci_col ci)).
                exact Hsame.
            }

            rewrite Hbest_not in Hdj_has.
            discriminate.

          + assert (Hci_not_best : ci_col ci <> best).
            {
              intro Heq.
              subst best.
              assert (eqb (ci_col ci) (ci_col ci) = true) as Hrefl.
              {
                apply (@eqb_true_iff Item H Item_eqb_laws).
                reflexivity.
              }
              rewrite Hrefl in Hci_best.
              discriminate.
            }

            specialize (Hsurv_cells ci Hci Hci_not_best).

            destruct (ci_color ci) as [x|] eqn:Hci_color.
            * assert (Hnd_r' : row_no_duplicate_columns r').
              {
                eapply row_no_duplicate_columns_from_problem_wf.
                - exact Hwf.
                - exact Hr'_p.
              }

              assert (Hcompat : colors_compatible (Some x) (ci_color dj) = true).
              {
                eapply row_color_ok_same_col_compatible.
                - exact Hnd_r'.
                - exact Hdj.
                - exact Hsame.
                - exact Hsurv_cells.
              }

              rewrite Hcompat in Hconf.
              simpl in Hconf.
              discriminate.
            * assert (Hdj_has : row_has_col (ci_col ci) r' = true).
              {
                eapply row_has_col_of_in.
                - exact Hdj.
                - rewrite (@eqb_sym_explicit Item H Item_eqb_laws
                            (ci_col dj) (ci_col ci)).
                  exact Hsame.
              }

              rewrite Hsurv_cells in Hdj_has.
              discriminate.

        - reflexivity.
      Qed.

      Lemma commit_other_cell_preserves_primary_if_not_col :
        forall chosen_col (ci : citem Item Color) (p : problem Item Color RowId) i,
          In i (primary_items p) ->
          eqb i (ci_col ci) = false ->
          In i (primary_items (commit_other_cell chosen_col ci p)).
      Proof.
        intros chosen_col ci p i Hi Hnot_col.
        unfold commit_other_cell.
        destruct (eqb (ci_col ci) chosen_col) eqn:Hchosen.
        - exact Hi.
        - unfold commit_cell.
          destruct (ci_color ci) as [x|] eqn:Hcolor.
          + unfold purify.
            simpl.
            exact Hi.
          + unfold cover, remove_primary.
            simpl.
            apply filter_In.
            split.
            * exact Hi.
            * rewrite Hnot_col.
              reflexivity.
      Qed.

      Lemma fold_commit_other_cell_preserves_primary_if_no_col :
        forall chosen_col cis (p : problem Item Color RowId) i,
          In i (primary_items p) ->
          (forall ci,
              In ci cis ->
              eqb i (ci_col ci) = false) ->
          In i
            (primary_items
              (fold_left
                  (fun acc ci => commit_other_cell chosen_col ci acc)
                  cis
                  p)).
      Proof.
        intros chosen_col cis.
        induction cis as [|ci cis IH]; intros p i Hi Hnot; simpl.
        - exact Hi.
        - apply IH.
          + apply commit_other_cell_preserves_primary_if_not_col.
            * exact Hi.
            * apply Hnot.
              left. reflexivity.
          + intros ci0 Hci0.
            apply Hnot.
            right. exact Hci0.
      Qed.

      Lemma commit_preserves_uncovered_primary :
        forall (p : problem Item Color RowId) best r i,
          problem_wf p ->
          In best (primary_items p) ->
          In r (rows_with_col best (rows p)) ->
          In i (primary_items p) ->
          row_has_col i r = false ->
          In i (primary_items (commit best r p)).
      Proof.
        intros p best r i Hwf Hbest Hr Hi Hri.
        unfold commit.

        apply fold_commit_other_cell_preserves_primary_if_no_col.
        - unfold cover, remove_primary.
          simpl.
          apply filter_In.
          split.
          + exact Hi.
          + destruct (eqb i best) eqn:Hi_best.
            * apply (@eqb_true_iff Item H Item_eqb_laws) in Hi_best.
              subst i.

              pose proof (rows_with_col_has_col best (rows p) r Hr) as Hbest_has.
              rewrite Hri in Hbest_has.
              discriminate.
            * reflexivity.

        - intros ci Hci.
          eapply row_has_col_false_no_cell.
          + exact Hri.
          + exact Hci.
      Qed.

      Lemma committed_row_avoids_chosen_primary :
        forall (p : problem Item Color RowId) best r r' i,
          problem_wf p ->
          In best (primary_items p) ->
          In r (rows_with_col best (rows p)) ->
          In i (primary_items p) ->
          row_has_col i r = true ->
          In r' (rows (commit best r p)) ->
          row_has_col i r' = false.
      Proof.
        intros p best r r' i Hwf Hbest Hr Hi Hri Hr'_commit.

        apply row_survives_commit_iff in Hr'_commit.
        destruct Hr'_commit as [_ [Hbest_not Hsurv_cells]].

        destruct (eqb i best) eqn:Hi_best.
        - apply (@eqb_true_iff Item H Item_eqb_laws) in Hi_best.
          subst i.
          exact Hbest_not.

        - unfold row_has_col in Hri.
          destruct (cell_on i r) as [ci|] eqn:Hcell; try discriminate.

          unfold cell_on in Hcell.
          apply find_some in Hcell.
          destruct Hcell as [Hci_in Hci_match].

          assert (Hci_col_eq_i : ci_col ci = i).
          {
            apply (@eqb_true_iff Item H Item_eqb_laws).
            exact Hci_match.
          }

          assert (Hci_not_best : ci_col ci <> best).
          {
            intro Hbad.
            rewrite Hbad in Hci_match.
            rewrite (@eqb_sym_explicit Item H Item_eqb_laws best i) in Hci_match.
            rewrite Hi_best in Hci_match.
            discriminate.
          }

          specialize (Hsurv_cells ci Hci_in Hci_not_best).

          assert (Hci_uncolored : ci_color ci = None).
          {
            destruct Hwf as [_ [_ [_ Huncolored]]].
            eapply Huncolored.
            - eapply rows_with_col_in_rows.
              exact Hr.
            - exact Hci_in.
            - rewrite Hci_col_eq_i.
              exact Hi.
          }

          rewrite Hci_uncolored in Hsurv_cells.
          rewrite Hci_col_eq_i in Hsurv_cells.
          exact Hsurv_cells.
      Qed.

      Lemma commit_extends_primary :
        forall (p : problem Item Color RowId) best r sol',
          problem_wf p ->
          In best (primary_items p) ->
          In r (rows_with_col best (rows p)) ->
          rows_from_problem (commit best r p) sol' ->
          primary_exactly_once (commit best r p) sol' ->
          primary_exactly_once p (r :: sol').
      Proof.
        intros p best r sol' Hwf Hbest Hr Hrows_tail Hprimary_tail.
        unfold primary_exactly_once in *.

        intros i Hi.

        destruct (row_has_col i r) eqn:Hri.
        - exists r.
          split.
          + simpl. left. reflexivity.
          + split.
            * exact Hri.
            * intros r0 Hr0 Hr0_has.
              simpl in Hr0.
              destruct Hr0 as [Hr0_eq | Hr0_tail].
              symmetry. exact Hr0_eq.
              -- assert (Hr0_commit : In r0 (rows (commit best r p))).
                {
                  unfold rows_from_problem in Hrows_tail.
                  rewrite Forall_forall in Hrows_tail.
                  apply Hrows_tail.
                  exact Hr0_tail.
                }

                assert (Havoid : row_has_col i r0 = false).
                {
                  eapply committed_row_avoids_chosen_primary.
                  - exact Hwf.
                  - exact Hbest.
                  - exact Hr.
                  - exact Hi.
                  - exact Hri.
                  - exact Hr0_commit.
                }
                rewrite Havoid in Hr0_has.
                discriminate.

        - assert (Hi_commit : In i (primary_items (commit best r p))).
          {
            eapply commit_preserves_uncovered_primary.
            - exact Hwf.
            - exact Hbest.
            - exact Hr.
            - exact Hi.
            - exact Hri.
          }

          specialize (Hprimary_tail i Hi_commit).
          destruct Hprimary_tail as [w [Hw_tail [Hw_has Huniq_tail]]].

          exists w.
          split.
          + simpl. right. exact Hw_tail.
          + split.
            * exact Hw_has.
            * intros r0 Hr0 Hr0_has.
              simpl in Hr0.
              destruct Hr0 as [Hr0_eq | Hr0_tail].
              -- subst r0.
                rewrite Hri in Hr0_has.
                discriminate.
              -- apply Huniq_tail.
                ++ exact Hr0_tail.
                ++ exact Hr0_has.
      Qed.

      Lemma choose_col_aux_in :
        forall (p : problem Item Color RowId) c cs n,
          In (choose_col_aux p c n cs) (c :: cs).
      Proof.
        intros p c cs.
        revert c.
        induction cs as [|i cs IH]; intros c n; simpl.
        - left. reflexivity.
        - destruct (Nat.ltb (col_len i p) n) eqn:Hlt.
          + right.
            apply IH.
          + specialize (IH c n).
            destruct IH as [Hin | Hin].
            * left. exact Hin.
            * right. right. exact Hin.
      Qed.

      Lemma commit_extends_solution :
        forall (p : problem Item Color RowId) best r sol',
          problem_wf p ->
          In best (primary_items p) ->
          In r (rows_with_col best (rows p)) ->
          valid_solution (commit best r p) sol' ->
          valid_solution p (r :: sol').
      Proof.
        intros p best r sol' Hwf Hbest Hr Hvalid_tail.
        destruct Hvalid_tail as [Hrows_tail [Hprimary_tail Hcompat_tail]].

        unfold valid_solution.
        split.
        - (* rows_from_problem *)
          unfold rows_from_problem in *.
          constructor.
          + eapply rows_with_col_in_rows.
            exact Hr.
          + apply Forall_forall.
            intros r' Hr'.
            rewrite Forall_forall in Hrows_tail.
            specialize (Hrows_tail r' Hr').
            eapply commit_rows_subset.
            exact Hrows_tail.

        - split.
          + (* primary_exactly_once *)
            eapply commit_extends_primary.
            * exact Hwf.
            * exact Hbest.
            * exact Hr.
            * exact Hrows_tail.
            * exact Hprimary_tail.

          + (* rows_pairwise_compatible *)
            unfold rows_pairwise_compatible in *.
            intros a b Ha Hb Hneq.
            simpl in Ha, Hb.

            destruct Ha as [Ha | Ha];
            destruct Hb as [Hb | Hb].
            * subst a. subst b. contradiction.

            * subst a.
              assert (Hb_rows_commit : In b (rows (commit best r p))).
              {
                unfold rows_from_problem in Hrows_tail.
                rewrite Forall_forall in Hrows_tail.
                apply Hrows_tail.
                exact Hb.
              }
              eapply commit_survivors_compatible.
              -- exact Hwf.
              -- exact Hr.
              -- exact Hb_rows_commit.

            * subst b.
              assert (Ha_rows_commit : In a (rows (commit best r p))).
              {
                unfold rows_from_problem in Hrows_tail.
                rewrite Forall_forall in Hrows_tail.
                apply Hrows_tail.
                exact Ha.
              }
              rewrite conflicts_with_symmetric.
              eapply commit_survivors_compatible.
              -- exact Hwf.
              -- exact Hr.
              -- exact Ha_rows_commit.

            * eapply Hcompat_tail.
              -- exact Ha.
              -- exact Hb.
              -- exact Hneq.
      Qed.

      (** ** Main soundness theorem

          [solve_sound] states that every solution returned by the solver is valid.

          This is a _partial correctness_ theorem: it says that returned answers are
          correct.  It does not claim that every valid solution is returned, nor that
          the fuel bound is sufficient.
      *)

      Theorem solve_sound :
        forall fuel p sol,
          problem_wf p ->
          In sol (solve fuel p) ->
          valid_solution p sol.
      Proof.
          induction fuel as [|fuel IH]; intros p sol Hwf Hin.
          - simpl in Hin. contradiction.
          - simpl in Hin.
            unfold solve in Hin.
            simpl in Hin.
            destruct (primary_items p) as [|c cs] eqn:Hprim.
            + simpl in Hin.
              destruct Hin as [Hsol | Hfalse].
              * subst sol.
                eapply empty_solution_valid_when_no_primaries; eauto.
              * contradiction.
            + unfold choose_col in Hin.
              rewrite Hprim in Hin.
              simpl in Hin.
              set (best := choose_col_aux p c (col_len c p) cs) in *.
              apply in_flat_map in Hin.
              destruct Hin as [r [Hr Hin_r]].
              apply in_map_iff in Hin_r.
              destruct Hin_r as [sol' [Hsol Hin_sol']].
              subst sol.
              assert (Hwf_commit : problem_wf (commit best r p)). { eapply commit_preserves_wf; eauto. }
            * assert (Htail : valid_solution (commit best r p) sol').
              {
                apply IH.
                - exact Hwf_commit.
                - unfold solve.
                  exact Hin_sol'.
              }
                eapply commit_extends_solution.
                -- exact Hwf.
                -- subst best.
                  rewrite Hprim.
                  apply choose_col_aux_in.
                -- exact Hr.
                -- exact Htail.
      Qed.

      (* end hide *)

    End Proofs.

  End FunctionalGDance.

(******************************************************************************)
(* Small executable examples                                                    *)
(******************************************************************************)

(** ** Worked examples and regression tests

    The following examples are intentionally kept in the generated documentation.

    They serve two purposes:

    - executable regression tests, since each expected result is checked by
      computation; and
    - modeling examples, showing how to construct exact-cover and colored-DLX
      problems directly from rows, primary items, colored items, and generated
      problem families.

    Readers who want to build their own Core problems should start here.
*)

Module Examples.

  Definition I := string.
  Definition C := nat.
  Definition R := nat.

  Definition u {I C : Type} (x : I) : citem I C := {| ci_col := x; ci_color := None |}.

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

  Definition demo_problem : problem I C R := Problem ["A"; "B"] [r1; r2; r3].
  Definition demo_expected : list (list R) := [[1; 2]].

  Program Definition solve_correct : solve_ids 5 demo_problem =demo_expected := _.


  (* Expected shape: [[1; 2]], up to row ordering determined by choose_col/search. *)

  Definition R1 : row I C R := Row 1 [u "A"; k "X" 7].
  Definition R6 : row I C R := Row 6 [u "A"; k "X" 9].

  Definition R2 : row I C R := Row 2 [u "B"; k "X" 7; k "Y" 1].
  Definition R3 : row I C R := Row 3 [u "B"; k "X" 9; k "Y" 2].

  Definition R4 : row I C R := Row 4 [u "C"; k "Y" 1].
  Definition R5 : row I C R := Row 5 [u "C"; k "Y" 2].

  Definition demo_problem_2 : problem I C R :=
    Problem ["A"; "B"; "C"] [R1; R6; R2; R3; R4; R5].

  Definition demo_solutions_2 : list (list R) := solve_ids 10 demo_problem_2.
  Program Definition sol_correct: solve_ids 10 demo_problem_2 = [[1; 2; 4]; [6; 3; 5]] := _.

  Definition R101 : row I C R := Row 101 [u "A"; k "X" 1].
  Definition R102 : row I C R := Row 102 [u "A"; k "X" 2].
  Definition R103 : row I C R := Row 103 [u "A"; k "X" 3].
  Definition R104 : row I C R := Row 104 [u "A"; k "X" 4].

  Definition R201 : row I C R := Row 201 [u "B"; k "X" 1; k "Y" 10].
  Definition R202 : row I C R := Row 202 [u "B"; k "X" 2; k "Y" 20].
  Definition R203 : row I C R := Row 203 [u "B"; k "X" 3; k "Y" 30].
  Definition R204 : row I C R := Row 204 [u "B"; k "X" 4; k "Y" 40].

  Definition R301 : row I C R := Row 301 [u "C"; k "Y" 10; k "Z" 100].
  Definition R302 : row I C R := Row 302 [u "C"; k "Y" 20; k "Z" 200].
  Definition R303 : row I C R := Row 303 [u "C"; k "Y" 30; k "Z" 300].
  Definition R304 : row I C R := Row 304 [u "C"; k "Y" 40; k "Z" 400].

  Definition R401 : row I C R := Row 401 [u "D"; k "Z" 100; k "W" 5].
  Definition R402 : row I C R := Row 402 [u "D"; k "Z" 200; k "W" 6].
  Definition R403 : row I C R := Row 403 [u "D"; k "Z" 300; k "W" 7].
  Definition R404 : row I C R := Row 404 [u "D"; k "Z" 400; k "W" 8].

  Definition R501 : row I C R := Row 501 [u "E"; k "W" 5; k "V" 11].
  Definition R502 : row I C R := Row 502 [u "E"; k "W" 6; k "V" 12].
  Definition R503 : row I C R := Row 503 [u "E"; k "W" 7; k "V" 13].
  Definition R504 : row I C R := Row 504 [u "E"; k "W" 8; k "V" 14].

  Definition R601 : row I C R := Row 601 [u "F"; k "V" 11].
  Definition R602 : row I C R := Row 602 [u "F"; k "V" 12].
  Definition R603 : row I C R := Row 603 [u "F"; k "V" 13].
  Definition R604 : row I C R := Row 604 [u "F"; k "V" 14].

  Definition demo_problem_large : problem I C R :=
    Problem
      ["A"; "B"; "C"; "D"; "E"; "F"]
      [ R101; R102; R103; R104;
        R201; R202; R203; R204;
        R301; R302; R303; R304;
        R401; R402; R403; R404;
        R501; R502; R503; R504;
        R601; R602; R603; R604 ].

  Definition demo_solutions_large : list (list R) := solve_ids 20 demo_problem_large.

  Program Definition sol_correct_large :
    solve_ids 20 demo_problem_large =
      [[101; 201; 301; 401; 501; 601];
      [102; 202; 302; 402; 502; 602];
      [103; 203; 303; 403; 503; 603];
      [104; 204; 304; 404; 504; 604]] := _.

  Definition MI := (nat * nat)%type.
  Definition MC := nat.
  Definition MR := nat.

  Definition mu (x : MI) : citem MI MC := u x.

  Definition block_row (id : MR) (xs : list MI) : row MI MC MR := Row id (map mu xs).

  (* Multiset:
    element 0 occurs twice: (0,0), (0,1)
    element 1 occurs twice: (1,0), (1,1)
    element 2 occurs once:  (2,0)
  *)

  Definition M00 : MI := (0, 0).
  Definition M01 : MI := (0, 1).
  Definition M10 : MI := (1, 0).
  Definition M11 : MI := (1, 1).
  Definition M20 : MI := (2, 0).

  Definition multiset_primary_items : list MI := [M00; M01; M10; M11; M20].

  Definition P1 : row MI MC MR := block_row 1 [M00; M10].
  Definition P2 : row MI MC MR := block_row 2 [M01; M11].
  Definition P3 : row MI MC MR := block_row 3 [M20].

  Definition P4 : row MI MC MR := block_row 4 [M00; M11].
  Definition P5 : row MI MC MR := block_row 5 [M01; M10].

  Definition P6 : row MI MC MR := block_row 6 [M00].
  Definition P7 : row MI MC MR := block_row 7 [M01].
  Definition P8 : row MI MC MR := block_row 8 [M10].
  Definition P9 : row MI MC MR := block_row 9 [M11].
  Definition P10 : row MI MC MR := block_row 10 [M20].

  Definition multiset_partition_problem : problem MI MC MR :=
    Problem
      multiset_primary_items
      [P1; P2; P3; P4; P5; P6; P7; P8; P9; P10].

  Definition mi_eqb (x y : MI) : bool := Nat.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

  Global Instance Eqb_MI : Eqb MI := { eqb := mi_eqb }.

  Global Instance Eqb_nat : Eqb nat := { eqb := Nat.eqb }.

  Program Definition multiset_partition_correct :
    solve_ids 10 multiset_partition_problem =
      [[3; 1; 2];
      [3; 1; 7; 9];
      [3; 4; 5];
      [3; 4; 7; 8];
      [3; 6; 5; 9];
      [3; 6; 8; 2];
      [3; 6; 8; 7; 9];
      [10; 1; 2];
      [10; 1; 7; 9];
      [10; 4; 5];
      [10; 4; 7; 8];
      [10; 6; 5; 9];
      [10; 6; 8; 2];
      [10; 6; 8; 7; 9]] := _.

End Examples.

End Core.

(** ** Sudoku-style problem generators

    [SudokuProblem] builds exact-cover problems for generalized Sudoku-like
    grids.

    The generated candidate universe contains one row for each possible placement
    of a symbol in a cell.  A row covers:

    - the cell constraint;
    - the row-symbol constraint;
    - the column-symbol constraint;
    - the box-symbol constraint.

    Two public encodings are provided:

    - [generalized_sudoku_problem_exact], where all Sudoku constraints are
      primary and therefore exactly-once;
    - [generalized_sudoku_problem_at_most], where cells are primary and
      row/column/box symbol constraints act as at-most-once secondary
      constraints.

    The at-most version is useful for rectangular generalized cases where row
    length, column height, box size, and alphabet size do not all coincide.

    The [*_with_givens] variants restrict the candidate universe according to
    fixed cell values.  The [generated_solution_rows] and
    [generated_solution_ids] helpers build a known solution from a function
    [row -> col -> sym].
*)

Module SudokuProblem.
  (* begin hide *)

  Import Core.

  Inductive GCol :=
  | Cell   : nat -> nat -> GCol
  | RowSym : nat -> nat -> GCol
  | ColSym : nat -> nat -> GCol
  | BoxSym : nat -> nat -> nat -> GCol.

  Definition gcol_eqb (a b : GCol) : bool :=
    match a, b with
    | Cell r1 c1, Cell r2 c2 =>
        Nat.eqb r1 r2 && Nat.eqb c1 c2
    | RowSym r1 s1, RowSym r2 s2 =>
        Nat.eqb r1 r2 && Nat.eqb s1 s2
    | ColSym c1 s1, ColSym c2 s2 =>
        Nat.eqb c1 c2 && Nat.eqb s1 s2
    | BoxSym br1 bc1 s1, BoxSym br2 bc2 s2 =>
        Nat.eqb br1 br2 && Nat.eqb bc1 bc2 && Nat.eqb s1 s2
    | _, _ => false
    end.

  Global Instance Eqb_GCol : Eqb GCol := {
    eqb := gcol_eqb
  }.

  Definition SColor := nat.
  Definition SRowId := nat.

  Definition su (x : GCol) : citem GCol SColor :=
    {| ci_col := x; ci_color := None |}.

  Definition rows_count (R r : nat) : nat := R * r.
  Definition cols_count (C c : nat) : nat := C * c.
  Definition box_size  (r c : nat) : nat := r * c.

  Definition max3 (a b c : nat) : nat :=
    Nat.max a (Nat.max b c).

  Definition alphabet_size (R C r c : nat) : nat :=
    max3 (rows_count R r) (cols_count C c) (box_size r c).

  Definition row_indices (R r : nat) : list nat :=
    seq 0 (rows_count R r).

  Definition col_indices (C c : nat) : list nat :=
    seq 0 (cols_count C c).

  Definition symbols (R C r c : nat) : list nat :=
    seq 0 (alphabet_size R C r c).

  Definition box_row_of (r row : nat) : nat :=
    row / r.

  Definition box_col_of (c col : nat) : nat :=
    col / c.

  Definition candidate_id
    (R C r c row col sym : nat)
    : SRowId :=
    ((row * cols_count C c + col) * alphabet_size R C r c) + sym.

  Definition candidate_items
    (R C r c row col sym : nat)
    : list GCol :=
    [
      Cell row col;
      RowSym row sym;
      ColSym col sym;
      BoxSym (box_row_of r row) (box_col_of c col) sym
    ].

  Definition candidate_row
    (R C r c row_ix col_ix sym : nat)
    : row GCol SColor SRowId :=
    {|
      row_id :=
        candidate_id R C r c row_ix col_ix sym;

      row_items :=
        map su (candidate_items R C r c row_ix col_ix sym)
    |}.

  Definition all_cells
    (R C r c : nat)
    : list GCol :=
    flat_map
      (fun row =>
        map (fun col => Cell row col) (col_indices C c))
      (row_indices R r).

  Definition all_row_symbol_constraints
    (R C r c : nat)
    : list GCol :=
    flat_map
      (fun row =>
        map (fun sym => RowSym row sym) (symbols R C r c))
      (row_indices R r).

  Definition all_col_symbol_constraints
    (R C r c : nat)
    : list GCol :=
    flat_map
      (fun col =>
        map (fun sym => ColSym col sym) (symbols R C r c))
      (col_indices C c).

  Definition all_box_symbol_constraints
    (R C r c : nat)
    : list GCol :=
    flat_map
      (fun br =>
        flat_map
          (fun bc =>
            map (fun sym => BoxSym br bc sym) (symbols R C r c))
          (seq 0 C))
      (seq 0 R).

  Definition all_sudoku_constraints
    (R C r c : nat)
    : list GCol :=
    all_cells R C r c ++
    all_row_symbol_constraints R C r c ++
    all_col_symbol_constraints R C r c ++
    all_box_symbol_constraints R C r c.

  Definition all_candidate_rows
    (R C r c : nat)
    : list (row GCol SColor SRowId) :=
    flat_map
      (fun row =>
        flat_map
          (fun col =>
            map
              (fun sym => candidate_row R C r c row col sym)
              (symbols R C r c))
          (col_indices C c))
      (row_indices R r).

  (* General rectangular Sudoku-like encoding:
     - every cell must be filled exactly once;
     - row/column/box symbol constraints are at-most-once. *)
  Definition generalized_sudoku_problem_at_most
    (R C r c : nat)
    : problem GCol SColor SRowId :=
    Problem
      (all_cells R C r c)
      (all_candidate_rows R C r c).

  (* Strict exact Sudoku encoding:
     - every cell exactly once;
     - every row-symbol exactly once;
     - every column-symbol exactly once;
     - every box-symbol exactly once.

     This is appropriate when row length, column height, box size,
     and alphabet size match. *)
  Definition generalized_sudoku_problem_exact
    (R C r c : nat)
    : problem GCol SColor SRowId :=
    Problem
      (all_sudoku_constraints R C r c)
      (all_candidate_rows R C r c).

  (* Givens restrict the candidate universe.
     givens row col = Some sym means that cell is fixed to sym.
     givens row col = None means all symbols are allowed. *)
  Definition symbols_for_cell
    (R C r c : nat)
    (givens : nat -> nat -> option nat)
    (row col : nat)
    : list nat :=
    match givens row col with
    | Some sym => [sym]
    | None => symbols R C r c
    end.

  Definition all_candidate_rows_with_givens
    (R C r c : nat)
    (givens : nat -> nat -> option nat)
    : list (row GCol SColor SRowId) :=
    flat_map
      (fun row =>
        flat_map
          (fun col =>
            map
              (fun sym => candidate_row R C r c row col sym)
              (symbols_for_cell R C r c givens row col))
          (col_indices C c))
      (row_indices R r).

  Definition generalized_sudoku_problem_at_most_with_givens
    (R C r c : nat)
    (givens : nat -> nat -> option nat)
    : problem GCol SColor SRowId :=
    Problem
      (all_cells R C r c)
      (all_candidate_rows_with_givens R C r c givens).

  Definition generalized_sudoku_problem_exact_with_givens
    (R C r c : nat)
    (givens : nat -> nat -> option nat)
    : problem GCol SColor SRowId :=
    Problem
      (all_sudoku_constraints R C r c)
      (all_candidate_rows_with_givens R C r c givens).

  (* Optional: generate one intended solved grid as selected candidate rows. *)
  Definition generated_solution_rows
    (R C r c : nat)
    (sym_at : nat -> nat -> nat)
    : list (row GCol SColor SRowId) :=
    flat_map
      (fun row =>
        map
          (fun col =>
            candidate_row R C r c row col (sym_at row col))
          (col_indices C c))
      (row_indices R r).

  Definition generated_solution_ids
    (R C r c : nat)
    (sym_at : nat -> nat -> nat)
    : list SRowId :=
    map row_id (generated_solution_rows R C r c sym_at).

    (* end hide *)

End SudokuProblem.

Module SudokuProblemExamples.

  Import Core.
  Import SudokuProblem.

  (* begin hide *)


  (******************************************************************************)
  (* 1. generalized_sudoku_problem_at_most                                       *)
  (*                                                                            *)
  (* Shape: R=1 C=2 r=1 c=1                                                     *)
  (* Grid: 1 row x 2 cols                                                       *)
  (* Alphabet size = max(row length 2, col height 1, box size 1) = 2            *)
  (*                                                                            *)
  (* Cells are primary/exactly once. Row/col/box-symbol constraints are          *)
  (* at-most-once.                                                              *)
  (******************************************************************************)

  Definition rect_at_most_problem : problem GCol SColor SRowId :=
    generalized_sudoku_problem_at_most 1 2 1 1.

  Definition rect_at_most_solutions : list (list SRowId) :=
    solve_ids 10 rect_at_most_problem.

  Example rect_at_most_expected :
    rect_at_most_solutions =
      [[0; 3];
       [1; 2]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* 2. generalized_sudoku_problem_exact                                         *)
  (*                                                                            *)
  (* Shape: R=2 C=1 r=1 c=2                                                     *)
  (* Grid: 2 rows x 2 cols                                                       *)
  (* Box shape: 1 x 2 horizontal boxes                                           *)
  (* Alphabet size = 2                                                           *)
  (*                                                                            *)
  (* Here row length = column height = box size = alphabet size = 2, so exact    *)
  (* constraints are satisfiable.                                                *)
  (******************************************************************************)

  Definition exact_2x2_problem : problem GCol SColor SRowId :=
    generalized_sudoku_problem_exact 2 1 1 2.

  Definition exact_2x2_solutions : list (list SRowId) :=
    solve_ids 10 exact_2x2_problem.

  Example exact_2x2_expected :
    exact_2x2_solutions =
      [[0; 3; 5; 6];
       [1; 2; 4; 7]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* 3. generalized_sudoku_problem_at_most_with_givens                           *)
  (*                                                                            *)
  (* Same rectangular at-most problem as #1, but with cell (0,0) fixed to 0.     *)
  (******************************************************************************)

  Definition given_00_is_0 (row col : nat) : option nat :=
    if Nat.eqb row 0 && Nat.eqb col 0
    then Some 0
    else None.

  Definition rect_at_most_given_problem : problem GCol SColor SRowId :=
    generalized_sudoku_problem_at_most_with_givens 1 2 1 1 given_00_is_0.

  Definition rect_at_most_given_solutions : list (list SRowId) :=
    solve_ids 10 rect_at_most_given_problem.

  Example rect_at_most_with_givens_expected :
    rect_at_most_given_solutions =
      [[0; 3]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* 4. generalized_sudoku_problem_exact_with_givens                             *)
  (*                                                                            *)
  (* Same exact 2x2 problem as #2, with cell (0,0) fixed to 0.                   *)
  (* This leaves exactly one solution.                                           *)
  (******************************************************************************)

  Definition exact_2x2_given_problem : problem GCol SColor SRowId :=
    generalized_sudoku_problem_exact_with_givens 2 1 1 2 given_00_is_0.

  Definition exact_2x2_given_solutions : list (list SRowId) :=
    solve_ids 10 exact_2x2_given_problem.

  Example exact_with_givens_expected :
    exact_2x2_given_solutions =
      [[0; 3; 5; 6]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* 5. generated_solution_rows                                                  *)
  (*                                                                            *)
  (* Generate the checkerboard solution:                                         *)
  (*                                                                            *)
  (*   0 1                                                                      *)
  (*   1 0                                                                      *)
  (*                                                                            *)
  (* for the exact 2x2 shape.                                                    *)
  (******************************************************************************)

  Definition checker2_sym_at (row col : nat) : nat :=
    Nat.modulo (row + col) 2.

  Definition checker2_solution_rows : list (row GCol SColor SRowId) :=
    generated_solution_rows 2 1 1 2 checker2_sym_at.

  Definition checker2_solution_ids : list SRowId :=
    map row_id checker2_solution_rows.

  Example generated_solution_rows_expected :
    checker2_solution_ids =
      [0; 3; 5; 6].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* 6. Full givens from generated_solution_rows                                 *)
  (*                                                                            *)
  (* This verifies that the generated solution, when used as full givens,        *)
  (* is exactly what the solver returns.                                         *)
  (******************************************************************************)

  Definition checker2_full_givens (row col : nat) : option nat :=
    Some (checker2_sym_at row col).

  Definition checker2_full_problem : problem GCol SColor SRowId :=
    generalized_sudoku_problem_exact_with_givens 2 1 1 2 checker2_full_givens.

  Definition checker2_full_solutions : list (list SRowId) :=
    solve_ids 10 checker2_full_problem.

  Example generated_solution_as_full_givens_expected :
    checker2_full_solutions =
      [checker2_solution_ids].
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  (******************************************************************************)
  (* generated_solution_ids                                                      *)
  (*                                                                            *)
  (* Generate the checkerboard solution IDs for the exact 2x2 shape:             *)
  (*                                                                            *)
  (*   0 1                                                                       *)
  (*   1 0                                                                       *)
  (*                                                                            *)
  (* Shape parameters:                                                           *)
  (*   R = 2, C = 1, r = 1, c = 2                                                *)
  (*                                                                            *)
  (* Grid size:                                                                  *)
  (*   rows = R * r = 2                                                          *)
  (*   cols = C * c = 2                                                          *)
  (*   alphabet size = 2                                                         *)
  (*                                                                            *)
  (* The candidate_id formula gives:                                             *)
  (*                                                                            *)
  (*   cell (0,0), sym 0 -> id 0                                                 *)
  (*   cell (0,1), sym 1 -> id 3                                                 *)
  (*   cell (1,0), sym 1 -> id 5                                                 *)
  (*   cell (1,1), sym 0 -> id 6                                                 *)
  (*                                                                            *)
  (* So the generated solution IDs are:                                          *)
  (*                                                                            *)
  (*   [0; 3; 5; 6]                                                              *)
  (******************************************************************************)

  Definition checker2_exact_sym_at (row col : nat) : nat :=
    Nat.modulo (row + col) 2.

  Definition checker2_exact_solution_ids : list SudokuProblem.SRowId :=
    SudokuProblem.generated_solution_ids 2 1 1 2 checker2_exact_sym_at.

  Example checker2_exact_solution_ids_expected :
    checker2_exact_solution_ids = [0; 3; 5; 6].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* generated_solution_ids used as expected solver output                       *)
  (*                                                                            *)
  (* Here we turn the generated checkerboard solution into full givens:           *)
  (*                                                                            *)
  (*   givens row col = Some (checker2_exact_sym_at row col)                     *)
  (*                                                                            *)
  (* This means every cell is fixed to the generated solution. Therefore the      *)
  (* exact Sudoku problem should have exactly one solver result, namely the       *)
  (* generated solution ID list.                                                 *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*                                                                            *)
  (*   [SudokuProblem.generated_solution_ids 2 1 1 2 checker2_exact_sym_at]       *)
  (*                                                                            *)
  (* which computes to:                                                          *)
  (*                                                                            *)
  (*   [[0; 3; 5; 6]]                                                            *)
  (******************************************************************************)

  Definition checker2_exact_full_givens (row col : nat) : option nat :=
    Some (checker2_exact_sym_at row col).

  Definition checker2_exact_full_problem
    : problem SudokuProblem.GCol SudokuProblem.SColor SudokuProblem.SRowId :=
    SudokuProblem.generalized_sudoku_problem_exact_with_givens
      2 1 1 2
      checker2_exact_full_givens.

  Definition checker2_exact_full_solutions : list (list SudokuProblem.SRowId) :=
    solve_ids 10 checker2_exact_full_problem.

  Example checker2_exact_full_solutions_expected :
    checker2_exact_full_solutions =
      [SudokuProblem.generated_solution_ids 2 1 1 2 checker2_exact_sym_at].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* generated_solution_ids, exact computed form                                 *)
  (*                                                                            *)
  (* This is the same verification as above, but with the expected list written   *)
  (* out explicitly. This is useful as a regression test because it will fail if  *)
  (* candidate_id, traversal order, or generated_solution_ids changes.            *)
  (******************************************************************************)

  Example checker2_exact_full_solutions_explicit_expected :
    checker2_exact_full_solutions = [[0; 3; 5; 6]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  (* end hide *)

End SudokuProblemExamples.

From Stdlib Require Import List String Ascii Arith Bool.
Open Scope string_scope.

(** ** Generated warehouse / scheduling-style problems

    This module builds warehouse-style exact-cover problems.

    Primary columns represent required items.  Source columns appear in rows as
    secondary constraints and may be colored.  This models situations such as
    assigning items, tasks, or jobs to sources, machines, workers, or time slots.

    The guaranteed-k constructors generate a family of witness solutions by
    deterministically partitioning items among sources.  The construction
    guarantees at least [k] intended solutions by design.

    In this file we expose the generator as a public API and rely on the generic
    solver soundness theorem for returned-solution validity.  Deeper generator
    guarantees may be proved separately and reused rather than duplicated here.
*)

Module Guaranteed_K_Warehouse.

  Import Core.

  (* begin hide *)

  (******************************************************************************)
  (* Basic string/name generation                                                *)
  (******************************************************************************)

  Definition ascii_of_digit (d : nat) : ascii :=
    match d with
    | 0 => "0"%char | 1 => "1"%char | 2 => "2"%char
    | 3 => "3"%char | 4 => "4"%char | 5 => "5"%char
    | 6 => "6"%char | 7 => "7"%char | 8 => "8"%char
    | _ => "9"%char
    end.

  Fixpoint digits_rev_fuel (fuel n : nat) : list nat :=
    match fuel with
    | 0 => []
    | S fuel' =>
        let d := Nat.modulo n 10 in
        if Nat.ltb n 10 then [d]
        else d :: digits_rev_fuel fuel' (Nat.div n 10)
    end.

  Fixpoint string_of_ascii_list (xs : list ascii) : string :=
    match xs with
    | [] => EmptyString
    | x :: xs' => String x (string_of_ascii_list xs')
    end.

  Definition nat_to_string (n : nat) : string :=
    string_of_ascii_list
      (List.map ascii_of_digit
        (List.rev (digits_rev_fuel (S n) n))).

  Definition label (prefix : string) (i : nat) : string :=
    String.append prefix (nat_to_string (S i)).

  Definition generated_names (prefix : string) (n : nat) : list string :=
    List.map (label prefix) (seq 0 n).

  Definition indexed {A : Type} (xs : list A) : list (nat * A) :=
    combine (seq 0 (List.length xs)) xs.

  Definition nth_option {A} (xs : list A) (i : nat) : option A :=
    nth_error xs i.

  Definition choose_color
    (colors : list string)
    (i : nat)
    : option string :=
    match List.length colors with
    | 0 => None
    | len => nth_option colors (Nat.modulo i len)
    end.


  (******************************************************************************)
  (* Core warehouse row model                                                  *)
  (*                                                                            *)
  (* Item columns are primary and always uncolored.                              *)
  (* Source columns are secondary and may be uncolored or colored.               *)
  (*                                                                            *)
  (* If source_color = None, the source behaves like an at-most-once secondary.   *)
  (* If source_color = Some c, rows using the same source with the same color     *)
  (* may coexist, matching colored-DLX purification semantics.                   *)
  (******************************************************************************)

  Definition WItem := string.
  Definition WColor := string.
  Definition WRowId := nat.

  Definition primary_item_citem (item : string) : citem WItem WColor :=
    CItem item None.

  Definition secondary_source_citem
    (src : string)
    (source_color : option string)
    : citem WItem WColor :=
    CItem src source_color.

  Definition warehouse_row
    (id : WRowId)
    (src : string)
    (items : list string)
    (_product_color : option string)
    (source_color : option string)
    : row WItem WColor WRowId :=
    Row
      id
      (List.map primary_item_citem items ++
       [secondary_source_citem src source_color]).


  (******************************************************************************)
  (* Free/generated colored row universe                                         *)
  (*                                                                            *)
  (* This is the "problem-space" style generator. It creates many candidate rows *)
  (* using a deterministic parity rule.                                          *)
  (******************************************************************************)

  Definition generated_colored_row_id
    (n_product_colors si ci : nat)
    : WRowId :=
    si * n_product_colors + ci.

  Definition generated_colored_rows
    (items sources product_colors source_reqs : list string)
    : list (row WItem WColor WRowId) :=
    flat_map
      (fun '(si, src) =>
        flat_map
          (fun '(ci, pcolor) =>
            let carried :=
              List.map snd
                (List.filter
                  (fun '(ii, _) =>
                    Nat.eqb (Nat.modulo (si + ii + ci) 2) 0)
                  (indexed items))
            in
            match carried with
            | [] => []
            | _ =>
                let source_color := choose_color source_reqs si in
                [warehouse_row
                   (generated_colored_row_id (List.length product_colors) si ci)
                   src
                   carried
                   (Some pcolor)
                   source_color]
            end)
          (indexed product_colors))
      (indexed sources).

  Definition generated_colored_problem
    (n_items n_sources n_product_colors n_source_reqs : nat)
    : problem WItem WColor WRowId :=
    let items := generated_names "item" n_items in
    let sources := generated_names "src" n_sources in
    let product_colors := generated_names "color" n_product_colors in
    let source_reqs := generated_names "req" n_source_reqs in
    Problem
      items
      (generated_colored_rows items sources product_colors source_reqs).


  (******************************************************************************)
  (* Guaranteed-k witness construction                                           *)
  (*                                                                            *)
  (* Each witness_id deterministically partitions all items among the sources.   *)
  (* Therefore each witness contributes one intended exact-cover solution:        *)
  (*                                                                            *)
  (*   one row per source, collectively covering every item exactly once.         *)
  (******************************************************************************)

  Definition assigned_items_for_source_shifted
    (items : list string)
    (n_sources witness_id source_id : nat)
    : list string :=
    List.map snd
      (List.filter
        (fun '(ii, _) =>
          Nat.eqb
            (Nat.modulo (ii + witness_id) n_sources)
            source_id)
        (indexed items)).

  Definition guaranteed_row_id
    (n_sources witness_id source_id : nat)
    : WRowId :=
    witness_id * n_sources + source_id.

  Definition guaranteed_rows_for_witness
    (items sources : list string)
    (witness_id : nat)
    : list (row WItem WColor WRowId) :=
    List.map
      (fun '(si, src) =>
        warehouse_row
          (guaranteed_row_id (List.length sources) witness_id si)
          src
          (assigned_items_for_source_shifted
              items
              (List.length sources)
              witness_id
              si)
          None
          None)
      (indexed sources).

  Definition guaranteed_k_rows
    (items sources : list string)
    (k : nat)
    : list (row WItem WColor WRowId) :=
    flat_map
      (fun witness_id =>
        guaranteed_rows_for_witness items sources witness_id)
      (seq 0 k).

  Definition guaranteed_k_problem
    (n_items n_sources k : nat)
    : problem WItem WColor WRowId :=
    let items := generated_names "item" n_items in
    let sources := generated_names "src" n_sources in
    Problem
      items
      (guaranteed_k_rows items sources k).


  (******************************************************************************)
  (* Colored guaranteed-k witness construction                                   *)
  (*                                                                            *)
  (* Same guaranteed partition idea, but source columns may be colored.           *)
  (* This can allow additional valid combinations beyond the k witnesses, because *)
  (* compatible same-colored secondary source columns may coexist.                *)
  (******************************************************************************)

  Definition guaranteed_rows_for_witness_colored
    (items sources product_colors source_reqs : list string)
    (witness_id : nat)
    : list (row WItem WColor WRowId) :=
    List.map
      (fun '(si, src) =>
        let product_color :=
          choose_color product_colors (witness_id + si) in
        let source_color :=
          choose_color source_reqs si in
        warehouse_row
          (guaranteed_row_id (List.length sources) witness_id si)
          src
          (assigned_items_for_source_shifted
              items
              (List.length sources)
              witness_id
              si)
          product_color
          source_color)
      (indexed sources).

  Definition guaranteed_k_colored_rows
    (items sources product_colors source_reqs : list string)
    (k : nat)
    : list (row WItem WColor WRowId) :=
    flat_map
      (fun witness_id =>
        guaranteed_rows_for_witness_colored
          items sources product_colors source_reqs witness_id)
      (seq 0 k).

  Definition guaranteed_k_colored_problem
    (n_items n_sources n_product_colors n_source_reqs k : nat)
    : problem WItem WColor WRowId :=
    let items := generated_names "item" n_items in
    let sources := generated_names "src" n_sources in
    let product_colors := generated_names "color" n_product_colors in
    let source_reqs := generated_names "req" n_source_reqs in
    Problem
      items
      (guaranteed_k_colored_rows
        items sources product_colors source_reqs k).

  (* end hide *)

End Guaranteed_K_Warehouse.

Module Guaranteed_K_WarehouseExamples.

  Import Guaranteed_K_Warehouse.
  Import Core.

  (* begin hide *)

  (******************************************************************************)
  (* generated_colored_problem                                                   *)
  (*                                                                            *)
  (* This generates a small colored warehouse candidate universe.                 *)
  (*                                                                            *)
  (* Parameters:                                                                 *)
  (*   n_items          = 2                                                       *)
  (*   n_sources        = 1                                                       *)
  (*   n_product_colors = 2                                                       *)
  (*   n_source_reqs    = 1                                                       *)
  (*                                                                            *)
  (* Generated rows:                                                             *)
  (*   row 0 covers item1 and source src1:req1                                   *)
  (*   row 1 covers item2 and source src1:req1                                   *)
  (*                                                                            *)
  (* Because the shared source is colored with the same req color, both rows may  *)
  (* coexist. Therefore the unique solution is [0; 1].                            *)
  (******************************************************************************)

  Definition warehouse_generated_small_problem
    : problem WItem WColor WRowId :=
    generated_colored_problem 2 1 2 1.

  Definition warehouse_generated_small_solutions : list (list WRowId) :=
    solve_ids 10 warehouse_generated_small_problem.

  Example warehouse_generated_small_expected :
    warehouse_generated_small_solutions = [[0; 1]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* guaranteed_k_problem                                                        *)
  (*                                                                            *)
  (* Uncolored source columns behave as at-most-once secondary constraints.       *)
  (*                                                                            *)
  (* Parameters:                                                                 *)
  (*   n_items   = 4                                                             *)
  (*   n_sources = 2                                                             *)
  (*   k         = 2                                                             *)
  (*                                                                            *)
  (* Witness 0:                                                                  *)
  (*   row 0 -> src1 carries item1,item3                                         *)
  (*   row 1 -> src2 carries item2,item4                                         *)
  (*                                                                            *)
  (* Witness 1:                                                                  *)
  (*   row 2 -> src1 carries item2,item4                                         *)
  (*   row 3 -> src2 carries item1,item3                                         *)
  (*                                                                            *)
  (* Because sources are uncolored here, cross-witness rows using the same source *)
  (* conflict. The solver returns the two intended witness solutions.             *)
  (*                                                                            *)
  (* Expected exact solver order:                                                *)
  (*   [[0; 1]; [3; 2]]                                                          *)
  (******************************************************************************)

  Definition warehouse_guaranteed_2x2_problem
    : problem WItem WColor WRowId :=
    guaranteed_k_problem 4 2 2.

  Definition warehouse_guaranteed_2x2_solutions : list (list WRowId) :=
    solve_ids 10 warehouse_guaranteed_2x2_problem.

  Example warehouse_guaranteed_2x2_expected :
    warehouse_guaranteed_2x2_solutions =
      [[0; 1];
       [3; 2]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* guaranteed_k_problem, single-source exact k check                            *)
  (*                                                                            *)
  (* With one source, every witness row covers all items.                         *)
  (* Therefore k witnesses produce exactly k singleton solutions.                 *)
  (*                                                                            *)
  (* Parameters:                                                                 *)
  (*   n_items   = 3                                                             *)
  (*   n_sources = 1                                                             *)
  (*   k         = 4                                                             *)
  (*                                                                            *)
  (* Expected:                                                                   *)
  (*   [[0]; [1]; [2]; [3]]                                                      *)
  (******************************************************************************)

  Definition warehouse_guaranteed_single_source_problem
    : problem WItem WColor WRowId :=
    guaranteed_k_problem 3 1 4.

  Definition warehouse_guaranteed_single_source_solutions : list (list WRowId) :=
    solve_ids 10 warehouse_guaranteed_single_source_problem.

  Example warehouse_guaranteed_single_source_expected :
    warehouse_guaranteed_single_source_solutions =
      [[0]; [1]; [2]; [3]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* guaranteed_k_colored_problem                                                *)
  (*                                                                            *)
  (* Colored source columns use Core/color purification semantics.              *)
  (* Rows that share a source with the same source color may coexist.             *)
  (*                                                                            *)
  (* Parameters:                                                                 *)
  (*   n_items          = 4                                                       *)
  (*   n_sources        = 2                                                       *)
  (*   n_product_colors = 2                                                       *)
  (*   n_source_reqs    = 1                                                       *)
  (*   k                = 2                                                       *)
  (*                                                                            *)
  (* This still guarantees at least the two witness solutions, but because both   *)
  (* sources receive the same req color, compatible cross-witness combinations    *)
  (* are also valid.                                                             *)
  (*                                                                            *)
  (* Expected exact solver order:                                                *)
  (*   [[0; 1]; [0; 2]; [3; 1]; [3; 2]]                                          *)
  (******************************************************************************)

  Definition warehouse_guaranteed_colored_2x2_problem
    : problem WItem WColor WRowId :=
    guaranteed_k_colored_problem 4 2 2 1 2.

  Definition warehouse_guaranteed_colored_2x2_solutions : list (list WRowId) :=
    solve_ids 10 warehouse_guaranteed_colored_2x2_problem.

  Example warehouse_guaranteed_colored_2x2_expected :
    warehouse_guaranteed_colored_2x2_solutions =
      [[0; 1];
       [0; 2];
       [3; 1];
       [3; 2]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  (* end hide *)

End Guaranteed_K_WarehouseExamples.

(* From Stdlib Require Import List Arith Bool. *)
Import ListNotations.

(** ** Combinatorics problem generators

    This module exposes a collection of small exact-cover encodings suitable for
    demos and regression tests.

    Included families:

    - tuples and permutations;
    - combinations;
    - integer partitions;
    - set partitions;
    - multiset partitions;
    - N-Queens;
    - Langford pairs;
    - van der Waerden-style generated colorings.

    Some APIs encode each mathematical object as a single DLX row using the
    primary column [PickOne].  Others encode a mathematical object as a set of
    selected rows, such as N-Queens or set partitions.

    The browser demo decodes row identifiers into user-facing mathematical
    objects.  The row identifiers remain useful as a compact, stable trace of
    the exact-cover solution.
*)

Module Combinatorics.

  Import Core.

  (* begin hide *)


  (******************************************************************************)
  (* Column universe                                                             *)
  (******************************************************************************)

  Inductive CCol :=
  | Slot   : nat -> CCol
  | Value  : nat -> CCol
  | Occur  : nat -> CCol
  | PickOne : CCol
  | PartAt : nat -> nat -> CCol
  | QRow   : nat -> CCol
  | QCol   : nat -> CCol
  | QDiag1 : nat -> CCol
  | QDiag2 : nat -> CCol.

  Definition ccol_eqb (a b : CCol) : bool :=
    match a, b with
    | Slot i, Slot j => Nat.eqb i j
    | Value i, Value j => Nat.eqb i j
    | Occur i, Occur j => Nat.eqb i j
    | PickOne, PickOne => true
    | PartAt i x, PartAt j y => Nat.eqb i j && Nat.eqb x y
    | QRow i, QRow j => Nat.eqb i j
    | QCol i, QCol j => Nat.eqb i j
    | QDiag1 i, QDiag1 j => Nat.eqb i j
    | QDiag2 i, QDiag2 j => Nat.eqb i j
    | _, _ => false
    end.

  Global Instance Eqb_CCol : Eqb CCol := {
    eqb := ccol_eqb
  }.

  Definition CColor := nat.
  Definition CRowId := nat.

  Definition item (c : CCol) : citem CCol CColor :=
    CItem c None.

  Definition make_row (id : CRowId) (cols : list CCol)
    : row CCol CColor CRowId :=
    Row id (List.map item cols).

  Definition make_problem
    (primary : list CCol)
    (rows : list (row CCol CColor CRowId))
    : problem CCol CColor CRowId :=
    Problem primary rows.

  Definition slots (k : nat) : list CCol :=
    List.map Slot (seq 0 k).

  Definition values (n : nat) : list CCol :=
    List.map Value (seq 0 n).

  Definition occurs (n : nat) : list CCol :=
    List.map Occur (seq 0 n).


  (******************************************************************************)
  (* k-tuples from n values, reuse allowed                                       *)
  (*                                                                            *)
  (* Primary constraints:                                                        *)
  (*   each Slot s is filled exactly once.                                       *)
  (*                                                                            *)
  (* Values are encoded in row_id, not as columns, because values may repeat.     *)
  (******************************************************************************)

  Definition assignment_id (n slot value : nat) : CRowId :=
    slot * n + value.

  Definition tuple_row (n slot value : nat)
    : row CCol CColor CRowId :=
    make_row
      (assignment_id n slot value)
      [Slot slot].

  Definition assignment_rows_tuple (k n : nat)
    : list (row CCol CColor CRowId) :=
    flat_map
      (fun s =>
        List.map (fun v => tuple_row n s v) (seq 0 n))
      (seq 0 k).

  Definition tuple_problem (k n : nat)
    : problem CCol CColor CRowId :=
    make_problem
      (slots k)
      (assignment_rows_tuple k n).


  (******************************************************************************)
  (* k-permutations from n values, reuse forbidden                               *)
  (*                                                                            *)
  (* Primary constraints:                                                        *)
  (*   each Slot s is filled exactly once.                                       *)
  (*                                                                            *)
  (* Secondary/at-most-once constraints:                                         *)
  (*   Value v appears as an uncolored row item, so it cannot be reused.          *)
  (******************************************************************************)

  Definition permutation_row (n slot value : nat)
    : row CCol CColor CRowId :=
    make_row
      (assignment_id n slot value)
      [Slot slot; Value value].

  Definition assignment_rows_permutation (k n : nat)
    : list (row CCol CColor CRowId) :=
    flat_map
      (fun s =>
        List.map (fun v => permutation_row n s v) (seq 0 n))
      (seq 0 k).

  Definition permutation_problem (k n : nat)
    : problem CCol CColor CRowId :=
    make_problem
      (slots k)
      (assignment_rows_permutation k n).


  (******************************************************************************)
  (* Combinations                                                               *)
  (******************************************************************************)

  Fixpoint combinations_from
    (k start n : nat)
    : list (list nat) :=
    match k with
    | 0 => [[]]
    | S k' =>
        flat_map
          (fun v =>
            List.map
              (fun rest => v :: rest)
              (combinations_from k' (S v) n))
          (seq start (n - start))
    end.

  Definition combinations (k n : nat) : list (list nat) :=
    combinations_from k 0 n.

  Fixpoint combination_cols_aux
    (slot : nat)
    (xs : list nat)
    : list CCol :=
    match xs with
    | [] => []
    | x :: xs' =>
        Slot slot :: Value x :: combination_cols_aux (S slot) xs'
    end.

  Definition combination_row (id : CRowId) (xs : list nat)
    : row CCol CColor CRowId :=
    make_row id (PickOne :: combination_cols_aux 0 xs).

  Definition indexed {A : Type} (xs : list A) : list (nat * A) :=
    combine (seq 0 (List.length xs)) xs.

  Definition combination_problem (k n : nat)
    : problem CCol CColor CRowId :=
    make_problem
      [PickOne]
      (List.map
         (fun '(id, xs) => combination_row id xs)
         (indexed (combinations k n))).


  (******************************************************************************)
  (* Integer partitions                                                          *)
  (******************************************************************************)

  Fixpoint sum_nat (xs : list nat) : nat :=
    match xs with
    | [] => 0
    | x :: xs' => x + sum_nat xs'
    end.

  Fixpoint nonincreasing_from (prev : nat) (xs : list nat) : bool :=
    match xs with
    | [] => true
    | x :: xs' =>
        Nat.leb x prev && nonincreasing_from x xs'
    end.

  Definition nonincreasing (xs : list nat) : bool :=
    match xs with
    | [] => true
    | x :: xs' => nonincreasing_from x xs'
    end.

  Definition is_partition_of (n : nat) (xs : list nat) : bool :=
    Nat.eqb (sum_nat xs) n && nonincreasing xs.

  Fixpoint partitions_bounded
    (fuel n max_part : nat)
    : list (list nat) :=
    match fuel with
    | 0 => []
    | S fuel' =>
        match n with
        | 0 => [[]]
        | S _ =>
            flat_map
              (fun x =>
                List.map
                  (fun rest => x :: rest)
                  (partitions_bounded fuel' (n - x) x))
              (seq 1 max_part)
        end
    end.

  Definition partitions_of (n : nat) : list (list nat) :=
    List.filter
      (is_partition_of n)
      (partitions_bounded (S n) n n).

  Fixpoint partition_cols_aux
    (i : nat)
    (xs : list nat)
    : list CCol :=
    match xs with
    | [] => []
    | x :: xs' => PartAt i x :: partition_cols_aux (S i) xs'
    end.

  Definition partition_row (id : CRowId) (xs : list nat)
    : row CCol CColor CRowId :=
    make_row id (PickOne :: partition_cols_aux 0 xs).

  Definition partition_problem (n : nat)
    : problem CCol CColor CRowId :=
    make_problem
      [PickOne]
      (List.map
         (fun '(id, xs) => partition_row id xs)
         (indexed (partitions_of n))).

  Definition has_k_parts (k : nat) (xs : list nat) : bool :=
    Nat.eqb (List.length xs) k.

  Definition is_partition_of_k
    (n k : nat)
    (xs : list nat)
    : bool :=
    is_partition_of n xs && has_k_parts k xs.

  Definition partitions_of_k
    (n k : nat)
    : list (list nat) :=
    List.filter
      (is_partition_of_k n k)
      (partitions_bounded (S n) n n).

  Definition partition_problem_k
    (n k : nat)
    : problem CCol CColor CRowId :=
    make_problem
      [PickOne]
      (List.map
         (fun '(id, xs) => partition_row id xs)
         (indexed (partitions_of_k n k))).


  (******************************************************************************)
  (* Set partitions                                                              *)
  (******************************************************************************)

  Fixpoint subsets (xs : list nat) : list (list nat) :=
    match xs with
    | [] => [[]]
    | x :: xs' =>
        let ss := subsets xs' in
        ss ++ List.map (fun s => x :: s) ss
    end.

  Definition nonempty_subsets (xs : list nat) : list (list nat) :=
    List.filter
      (fun s => negb (Nat.eqb (List.length s) 0))
      (subsets xs).

  Definition set_partition_row (id : CRowId) (xs : list nat)
    : row CCol CColor CRowId :=
    make_row id (List.map Value xs).

  Definition generated_set (n : nat) : list nat :=
    seq 0 n.

  Definition set_partition_problem_values
    (elems : list nat)
    : problem CCol CColor CRowId :=
    make_problem
      (List.map Value elems)
      (List.map
         (fun '(id, xs) => set_partition_row id xs)
         (indexed (nonempty_subsets elems))).

  Definition set_partition_problem_generated
    (n : nat)
    : problem CCol CColor CRowId :=
    set_partition_problem_values (generated_set n).

  (* Backward-compatible name. *)
  Definition set_partition_problem
    (n : nat)
    : problem CCol CColor CRowId :=
    set_partition_problem_generated n.

  Definition set_partition_k_row
    (n slot block_id : nat)
    (xs : list nat)
    : row CCol CColor CRowId :=
    make_row
      (slot * Nat.pow 2 n + block_id)
      (Slot slot :: List.map Value xs).

  Definition set_partition_k_rows
    (k n : nat)
    : list (row CCol CColor CRowId) :=
    let elems := seq 0 n in
    let blocks := indexed (nonempty_subsets elems) in
    flat_map
      (fun s =>
        List.map
          (fun '(bid, b) => set_partition_k_row n s bid b)
          blocks)
      (seq 0 k).

  (******************************************************************************)
  (* Set partitions into exactly k blocks: explicit and generated APIs           *)
  (*                                                                            *)
  (* The blocks are labeled by Slot 0 ... Slot (k-1), so solutions may include    *)
  (* multiple labelings of the same mathematical set partition.                  *)
  (******************************************************************************)

  Definition set_partition_k_rows_values
    (k : nat)
    (elems : list nat)
    : list (row CCol CColor CRowId) :=
    let n := List.length elems in
    let blocks := indexed (nonempty_subsets elems) in
    flat_map
      (fun s =>
        List.map
          (fun '(bid, b) => set_partition_k_row n s bid b)
          blocks)
      (seq 0 k).

  Definition set_partition_k_problem_values
    (k : nat)
    (elems : list nat)
    : problem CCol CColor CRowId :=
    make_problem
      (slots k ++ List.map Value elems)
      (set_partition_k_rows_values k elems).

  Definition set_partition_k_problem_generated
    (k n : nat)
    : problem CCol CColor CRowId :=
    set_partition_k_problem_values k (generated_set n).

  (* Backward-compatible name. *)
  Definition set_partition_k_problem
    (k n : nat)
    : problem CCol CColor CRowId :=
    set_partition_k_problem_generated k n.

  (******************************************************************************)
  (* Multiset partitions                                                         *)
  (*                                                                            *)
  (* Occurrences are primary, so equal labels are represented by different        *)
  (* occurrence columns.                                                         *)
  (******************************************************************************)

  Definition multiset_partition_row (id : CRowId) (xs : list nat)
    : row CCol CColor CRowId :=
    make_row id (List.map Occur xs).

  Definition generated_multiset
    (n label_count : nat)
    : list nat :=
    match label_count with
    | 0 => []
    | S _ => List.map (fun i => Nat.modulo i label_count) (seq 0 n)
    end.

  Fixpoint repeat_nat (x count : nat) : list nat :=
    match count with
    | 0 => []
    | S count' => x :: repeat_nat x count'
    end.

  Fixpoint expand_counts_from
    (label : nat)
    (counts : list nat)
    : list nat :=
    match counts with
    | [] => []
    | c :: counts' =>
        repeat_nat label c ++ expand_counts_from (S label) counts'
    end.

  Definition expand_counts (counts : list nat) : list nat :=
    expand_counts_from 0 counts.

  Definition multiset_partition_problem (values0 : list nat)
    : problem CCol CColor CRowId :=
    let n := List.length values0 in
    let occs := seq 0 n in
    make_problem
      (occurs n)
      (List.map
         (fun '(id, xs) => multiset_partition_row id xs)
         (indexed (nonempty_subsets occs))).

  Definition multiset_partition_problem_generated
    (n label_count : nat)
    : problem CCol CColor CRowId :=
    multiset_partition_problem (generated_multiset n label_count).

  Definition multiset_partition_problem_counts
    (counts : list nat)
    : problem CCol CColor CRowId :=
    multiset_partition_problem (expand_counts counts).

  Definition multiset_partition_k_row
    (n slot block_id : nat)
    (xs : list nat)
    : row CCol CColor CRowId :=
    make_row
      (slot * Nat.pow 2 n + block_id)
      (Slot slot :: List.map Occur xs).

  Definition multiset_partition_k_rows
    (k : nat)
    (values0 : list nat)
    : list (row CCol CColor CRowId) :=
    let n := List.length values0 in
    let occs := seq 0 n in
    let blocks := indexed (nonempty_subsets occs) in
    flat_map
      (fun s =>
        List.map
          (fun '(bid, b) => multiset_partition_k_row n s bid b)
          blocks)
      (seq 0 k).

  Definition multiset_partition_k_problem
    (k : nat)
    (values0 : list nat)
    : problem CCol CColor CRowId :=
    let n := List.length values0 in
    make_problem
      (slots k ++ occurs n)
      (multiset_partition_k_rows k values0).

  Definition multiset_partition_k_problem_generated
    (k n label_count : nat)
    : problem CCol CColor CRowId :=
    multiset_partition_k_problem k (generated_multiset n label_count).

  Definition multiset_partition_k_problem_counts
    (k : nat)
    (counts : list nat)
    : problem CCol CColor CRowId :=
    multiset_partition_k_problem k (expand_counts counts).


  (******************************************************************************)
  (* N-Queens                                                                    *)
  (******************************************************************************)

  Definition diag1 (r c : nat) : nat :=
    r + c.

  Definition diag2 (n r c : nat) : nat :=
    r + (n - 1 - c).

  Definition queen_id (n r c : nat) : CRowId :=
    r * n + c.

  Definition queen_row (n r c : nat)
    : row CCol CColor CRowId :=
    make_row
      (queen_id n r c)
      [QRow r; QCol c; QDiag1 (diag1 r c); QDiag2 (diag2 n r c)].

  Definition queen_rows (n : nat)
    : list (row CCol CColor CRowId) :=
    flat_map
      (fun r =>
        List.map (fun c => queen_row n r c) (seq 0 n))
      (seq 0 n).

  Definition qrows (n : nat) : list CCol :=
    List.map QRow (seq 0 n).

  Definition qcols (n : nat) : list CCol :=
    List.map QCol (seq 0 n).

  Definition nqueens_problem (n : nat)
    : problem CCol CColor CRowId :=
    make_problem
      (qrows n ++ qcols n)
      (queen_rows n).

  (* end hide *)


  (** *** Langford pairs

      A Langford pairing of order [n] places two copies of each value [1..n] into
      [2*n] slots so that the two copies of [k] have exactly [k] slots between
      them.

      Each candidate row chooses a value [k] and a starting slot [start], covering:

      - [Slot start];
      - [Slot (start + k + 1)];
      - [Value k].

      The resulting exact cover fills all slots and uses each value exactly once.
  *)

  (******************************************************************************)
  (* Langford pairs                                                              *)
  (*                                                                            *)
  (* A Langford pairing of order n places two copies of each number k = 1..n     *)
  (* into 2n slots, with exactly k slots between the two copies of k.             *)
  (*                                                                            *)
  (* DLX encoding:                                                               *)
  (*                                                                            *)
  (*   Primary columns:                                                          *)
  (*     Slot 0 ... Slot (2n-1)                                                   *)
  (*     Value 1 ... Value n                                                     *)
  (*                                                                            *)
  (*   Candidate row for number k starting at position start:                    *)
  (*     covers Slot start                                                       *)
  (*            Slot (start + k + 1)                                              *)
  (*            Value k                                                          *)
  (*                                                                            *)
  (* This chooses each number exactly once and fills every slot exactly once.     *)
  (******************************************************************************)

  (* begin hide *)

  Definition langford_slots (n : nat) : list CCol :=
    List.map Slot (seq 0 (2 * n)).

  Definition langford_values (n : nat) : list CCol :=
    List.map Value (seq 1 n).

  Definition langford_row_id (n k start : nat) : CRowId :=
    (k - 1) * (2 * n) + start.

  Definition langford_second_pos (k start : nat) : nat :=
    start + k + 1.

  Definition langford_start_count (n k : nat) : nat :=
    2 * n - k - 1.

  Definition langford_row (n k start : nat)
    : row CCol CColor CRowId :=
    make_row
      (langford_row_id n k start)
      [ Slot start;
        Slot (langford_second_pos k start);
        Value k ].

  Definition langford_rows_for_value (n k : nat)
    : list (row CCol CColor CRowId) :=
    List.map
      (fun start => langford_row n k start)
      (seq 0 (langford_start_count n k)).

  Definition langford_rows (n : nat)
    : list (row CCol CColor CRowId) :=
    flat_map
      (fun k => langford_rows_for_value n k)
      (seq 1 n).

  Definition langford_problem (n : nat)
    : problem CCol CColor CRowId :=
    make_problem
      (langford_slots n ++ langford_values n)
      (langford_rows n).

  (* end hide *)

  (** *** Van der Waerden-style generated colorings

      This API generates all [q]-colorings of [0..n-1], filters out those with a
      monochromatic arithmetic progression of length [k], and exposes the remaining
      colorings as a [PickOne] exact-cover problem.

      This is intentionally a generated-solution-universe encoding.  The constraint
      "not all [k] positions in an arithmetic progression have the same color" is
      not naturally an at-most-one DLX constraint when [k >= 3].
  *)


  (******************************************************************************)
  (* Van der Waerden colorings                                                   *)
  (*                                                                            *)
  (* This is a generated valid-coloring universe.                                *)
  (*                                                                            *)
  (* We generate all q-colorings of positions 0..n-1, then keep only those that   *)
  (* avoid monochromatic arithmetic progressions of length k.                    *)
  (*                                                                            *)
  (* The resulting DLX problem has primary [PickOne], and each valid coloring     *)
  (* is represented as one candidate row. Therefore solve enumerates valid        *)
  (* AP-avoiding colorings.                                                       *)
  (*                                                                            *)
  (* Note: This is intentionally a "generated solution universe" encoding rather *)
  (* than a pairwise DLX constraint encoding, because "not all k positions are the same color" *)
  (* is not naturally an at-most-one constraint when k >= 3.      *)
  (******************************************************************************)

  (* begin hide *)

  Fixpoint colorings (n q : nat) : list (list nat) :=
    match n with
    | 0 => [[]]
    | S n' =>
        flat_map
          (fun color =>
            List.map
              (fun rest => color :: rest)
              (colorings n' q))
          (seq 0 q)
    end.

  Definition progression (start step k : nat) : list nat :=
    List.map
      (fun t => start + t * step)
      (seq 0 k).

  Definition progression_in_bounds
    (n start step k : nat)
    : bool :=
    Nat.ltb (start + (k - 1) * step) n.

  Definition arithmetic_progressions
    (n k : nat)
    : list (list nat) :=
    flat_map
      (fun start =>
        List.map
          (fun step => progression start step k)
          (List.filter
             (fun step => progression_in_bounds n start step k)
             (seq 1 n)))
      (seq 0 n).

  Definition color_at (colors : list nat) (pos : nat) : option nat :=
    nth_error colors pos.

  Definition same_color_at
    (colors : list nat)
    (color pos : nat)
    : bool :=
    match color_at colors pos with
    | Some c => Nat.eqb c color
    | None => false
    end.

  Definition monochromatic_progression
    (colors ap : list nat)
    : bool :=
    match ap with
    | [] => false
    | pos :: rest =>
        match color_at colors pos with
        | Some color =>
            forallb (same_color_at colors color) rest
        | None => false
        end
    end.

  Definition has_monochromatic_progression
    (n q k : nat)
    (colors : list nat)
    : bool :=
    existsb
      (monochromatic_progression colors)
      (arithmetic_progressions n k).

  Definition waerden_good_coloring
    (n q k : nat)
    (colors : list nat)
    : bool :=
    negb (has_monochromatic_progression n q k colors).

  Definition waerden_good_colorings
    (n q k : nat)
    : list (list nat) :=
    List.filter
      (waerden_good_coloring n q k)
      (colorings n q).

  Fixpoint coloring_cols_aux
    (pos : nat)
    (colors : list nat)
    : list CCol :=
    match colors with
    | [] => []
    | color :: colors' =>
        PartAt pos color :: coloring_cols_aux (S pos) colors'
    end.

  Definition waerden_coloring_row
    (id : CRowId)
    (colors : list nat)
    : row CCol CColor CRowId :=
    make_row
      id
      (PickOne :: coloring_cols_aux 0 colors).

  Definition waerden_rows
    (n q k : nat)
    : list (row CCol CColor CRowId) :=
    List.map
      (fun '(id, colors) => waerden_coloring_row id colors)
      (indexed (waerden_good_colorings n q k)).

  Definition waerden_problem
    (n q k : nat)
    : problem CCol CColor CRowId :=
    make_problem
      [PickOne]
      (waerden_rows n q k).

  (* end hide *)

End Combinatorics.

Module CombinatoricsGDanceExamples.

  Import Combinatorics.
  Import Core.

  (* begin hide *)

  (******************************************************************************)
  (* tuple_problem                                                               *)
  (*                                                                            *)
  (* k-tuples from n values, reuse allowed.                                      *)
  (*                                                                            *)
  (* Example: k = 2, n = 2                                                       *)
  (*                                                                            *)
  (* Slots:                                                                      *)
  (*   Slot 0, Slot 1                                                            *)
  (*                                                                            *)
  (* Values are encoded in row IDs, not as columns, so reuse is allowed.          *)
  (*                                                                            *)
  (* Row IDs:                                                                    *)
  (*   slot 0, value 0 -> 0                                                      *)
  (*   slot 0, value 1 -> 1                                                      *)
  (*   slot 1, value 0 -> 2                                                      *)
  (*   slot 1, value 1 -> 3                                                      *)
  (*                                                                            *)
  (* Expected tuples:                                                            *)
  (*   (0,0), (0,1), (1,0), (1,1)                                                *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*   [[0; 2]; [0; 3]; [1; 2]; [1; 3]]                                          *)
  (******************************************************************************)

  Definition tuple_2_2_problem : problem CCol CColor CRowId :=
    tuple_problem 2 2.

  Definition tuple_2_2_solutions : list (list CRowId) :=
    solve_ids 10 tuple_2_2_problem.

  Example tuple_2_2_expected :
    tuple_2_2_solutions =
      [[0; 2];
       [0; 3];
       [1; 2];
       [1; 3]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* permutation_problem                                                         *)
  (*                                                                            *)
  (* k-permutations from n values, reuse forbidden.                              *)
  (*                                                                            *)
  (* Example: k = 2, n = 3                                                       *)
  (*                                                                            *)
  (* Slots are primary. Values appear as uncolored secondary/at-most-once items. *)
  (* Therefore the two chosen rows must use different values.                    *)
  (*                                                                            *)
  (* Row IDs:                                                                    *)
  (*   slot 0 values 0,1,2 -> 0,1,2                                              *)
  (*   slot 1 values 0,1,2 -> 3,4,5                                              *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*   [[0; 4]; [0; 5]; [1; 3]; [1; 5]; [2; 3]; [2; 4]]                          *)
  (******************************************************************************)

  Definition permutation_2_3_problem : problem CCol CColor CRowId :=
    permutation_problem 2 3.

  Definition permutation_2_3_solutions : list (list CRowId) :=
    solve_ids 10 permutation_2_3_problem.

  Example permutation_2_3_expected :
    permutation_2_3_solutions =
      [[0; 4];
       [0; 5];
       [1; 3];
       [1; 5];
       [2; 3];
       [2; 4]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* combination_problem                                                         *)
  (*                                                                            *)
  (* Choose one k-combination from n values.                                     *)
  (*                                                                            *)
  (* Example: k = 2, n = 4                                                       *)
  (*                                                                            *)
  (* combinations 2 4 produces six combinations:                                 *)
  (*   [0;1], [0;2], [0;3], [1;2], [1;3], [2;3]                                  *)
  (*                                                                            *)
  (* The DLX problem has primary [PickOne], so each solution chooses exactly one  *)
  (* combination row.                                                            *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*   [[0]; [1]; [2]; [3]; [4]; [5]]                                            *)
  (******************************************************************************)

  Definition combination_2_4_problem : problem CCol CColor CRowId :=
    combination_problem 2 4.

  Definition combination_2_4_solutions : list (list CRowId) :=
    solve_ids 10 combination_2_4_problem.

  Example combination_2_4_expected :
    combination_2_4_solutions =
      [[0]; [1]; [2]; [3]; [4]; [5]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* partition_problem                                                           *)
  (*                                                                            *)
  (* Choose exactly one integer partition of n.                                  *)
  (*                                                                            *)
  (* Example: n = 4                                                              *)
  (*                                                                            *)
  (* partitions_of 4, in generator order:                                        *)
  (*   [2;1;1], [2;2], [3;1], [4]                                                *)
  (*                                                                            *)
  (* The DLX problem has primary [PickOne], so each solution chooses exactly one  *)
  (* partition row.                                                              *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*   [[0]; [1]; [2]; [3]]                                                      *)
  (******************************************************************************)

  Definition partition_4_problem : problem CCol CColor CRowId :=
    partition_problem 4.

  Definition partition_4_solutions : list (list CRowId) :=
    solve_ids 10 partition_4_problem.

  Example partition_4_expected :
    partition_4_solutions =
      [[0]; [1]; [2]; [3]; [4]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* partition_problem_k                                                         *)
  (*                                                                            *)
  (* Choose exactly one integer partition of n with exactly k parts.             *)
  (*                                                                            *)
  (* Example: n = 5, k = 2                                                       *)
  (*                                                                            *)
  (* partitions_of_k 5 2, in generator order:                                    *)
  (*   [3;2], [4;1]                                                              *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*   [[0]; [1]]                                                                *)
  (******************************************************************************)

  Definition partition_5_2_problem : problem CCol CColor CRowId :=
    partition_problem_k 5 2.

  Definition partition_5_2_solutions : list (list CRowId) :=
    solve_ids 10 partition_5_2_problem.

  Example partition_5_2_expected :
    partition_5_2_solutions =
      [[0]; [1]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Definition partition_5_5_problem : problem CCol CColor CRowId :=
    partition_problem_k 5 5.

  Definition partition_5_5_solutions : list (list CRowId) :=
    solve_ids 10 partition_5_5_problem.

  Example partition_5_5_expected :
    partition_5_5_solutions =
      [[0]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* set_partition_problem_generated                                             *)
  (*                                                                            *)
  (* Partition the generated set {0,1,2}.                                        *)
  (*                                                                            *)
  (* Candidate block order comes from nonempty_subsets [0;1;2]:                  *)
  (*                                                                            *)
  (*   id 0 -> [2]                                                               *)
  (*   id 1 -> [1]                                                               *)
  (*   id 2 -> [1;2]                                                             *)
  (*   id 3 -> [0]                                                               *)
  (*   id 4 -> [0;2]                                                             *)
  (*   id 5 -> [0;1]                                                             *)
  (*   id 6 -> [0;1;2]                                                           *)
  (*                                                                            *)
  (* Exact covers of {0,1,2}, in solver order:                                   *)
  (*                                                                            *)
  (*   [3;1;0]   = {0}, {1}, {2}                                                 *)
  (*   [3;2]     = {0}, {1,2}                                                    *)
  (*   [4;1]     = {0,2}, {1}                                                    *)
  (*   [5;0]     = {0,1}, {2}                                                    *)
  (*   [6]       = {0,1,2}                                                       *)
  (******************************************************************************)

  Definition set_partition_generated_3_problem
    : problem CCol CColor CRowId :=
    set_partition_problem_generated 3.

  Definition set_partition_generated_3_solutions : list (list CRowId) :=
    solve_ids 10 set_partition_generated_3_problem.

  Example set_partition_generated_3_expected :
    set_partition_generated_3_solutions =
      [[3; 1; 0];
       [3; 2];
       [4; 1];
       [5; 0];
       [6]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* set_partition_k_problem_generated                                           *)
  (*                                                                            *)
  (* Partition the generated set {0,1,2} into exactly k = 2 labeled blocks.       *)
  (*                                                                            *)
  (* Primary columns:                                                            *)
  (*   Slot 0, Slot 1, Value 0, Value 1, Value 2                                  *)
  (*                                                                            *)
  (* Block slots are labeled, so different labelings of the same mathematical     *)
  (* partition appear as different DLX solutions.                                *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*   [[0; 13]; [1; 12]; [2; 11]; [3; 10]; [4; 9]; [5; 8]]                      *)
  (******************************************************************************)

  Definition set_partition_k_generated_2_3_problem
    : problem CCol CColor CRowId :=
    set_partition_k_problem_generated 2 3.

  Definition set_partition_k_generated_2_3_solutions : list (list CRowId) :=
    solve_ids 10 set_partition_k_generated_2_3_problem.

  Example set_partition_k_generated_2_3_expected :
    set_partition_k_generated_2_3_solutions =
      [[0; 13];
       [1; 12];
       [2; 11];
       [3; 10];
       [4; 9];
       [5; 8]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* multiset_partition_problem_counts                                           *)
  (*                                                                            *)
  (* Partition a multiset represented by counts.                                 *)
  (*                                                                            *)
  (* Example counts: [2;1]                                                       *)
  (*   value 0 occurs twice                                                      *)
  (*   value 1 occurs once                                                       *)
  (*                                                                            *)
  (* The DLX encoding partitions occurrences, not labels, so there are three      *)
  (* occurrence columns: Occur 0, Occur 1, Occur 2.                               *)
  (*                                                                            *)
  (* Therefore the solver output has the same shape as set_partition_generated 3. *)
  (******************************************************************************)

  Definition multiset_partition_counts_2_1_problem
    : problem CCol CColor CRowId :=
    multiset_partition_problem_counts [2; 1].

  Definition multiset_partition_counts_2_1_solutions : list (list CRowId) :=
    solve_ids 10 multiset_partition_counts_2_1_problem.

  Example multiset_partition_counts_2_1_expected :
    multiset_partition_counts_2_1_solutions =
      [[3; 1; 0];
       [3; 2];
       [4; 1];
       [5; 0];
       [6]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* multiset_partition_k_problem_generated                                      *)
  (*                                                                            *)
  (* Partition a generated multiset of length 3 into exactly 2 labeled blocks.    *)
  (*                                                                            *)
  (* generated_multiset 3 2 = [0;1;0]                                            *)
  (*                                                                            *)
  (* Again, the DLX encoding partitions occurrences, so the expected row-id       *)
  (* structure matches the set_partition_k example over 3 occurrences.            *)
  (******************************************************************************)

  Definition multiset_partition_k_generated_2_3_2_problem
    : problem CCol CColor CRowId :=
    multiset_partition_k_problem_generated 2 3 2.

  Definition multiset_partition_k_generated_2_3_2_solutions : list (list CRowId) :=
    solve_ids 10 multiset_partition_k_generated_2_3_2_problem.

  Example multiset_partition_k_generated_2_3_2_expected :
    multiset_partition_k_generated_2_3_2_solutions =
      [[0; 13];
       [1; 12];
       [2; 11];
       [3; 10];
       [4; 9];
       [5; 8]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* nqueens_problem                                                             *)
  (*                                                                            *)
  (* 4-Queens.                                                                   *)
  (*                                                                            *)
  (* Primary columns:                                                            *)
  (*   QRow 0..3 and QCol 0..3                                                   *)
  (*                                                                            *)
  (* Diagonals appear in rows but not as primary columns, so they behave as       *)
  (* at-most-once constraints.                                                   *)
  (*                                                                            *)
  (* Row ID formula:                                                             *)
  (*   queen_id n r c = r * n + c                                                *)
  (*                                                                            *)
  (* The two 4-Queens solutions are:                                             *)
  (*                                                                            *)
  (*   columns [1;3;0;2] -> ids [1;7;8;14]                                       *)
  (*   columns [2;0;3;1] -> ids [2;4;11;13]                                      *)
  (******************************************************************************)

  Definition nqueens_4_problem : problem CCol CColor CRowId :=
    nqueens_problem 4.

  Definition nqueens_4_solutions : list (list CRowId) :=
    solve_ids 10 nqueens_4_problem.

  Example nqueens_4_expected :
    nqueens_4_solutions =
      [[1; 7; 8; 14];
       [2; 4; 11; 13]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  (******************************************************************************)
  (* langford_problem                                                            *)
  (*                                                                            *)
  (* Langford pairs of order n = 3.                                              *)
  (*                                                                            *)
  (* Primary columns:                                                            *)
  (*   Slot 0 ... Slot 5                                                         *)
  (*   Value 1 ... Value 3                                                       *)
  (*                                                                            *)
  (* Candidate row ID formula:                                                   *)
  (*   langford_row_id n k start = (k - 1) * (2 * n) + start                     *)
  (*                                                                            *)
  (* The two oriented Langford pairings for n = 3 are:                            *)
  (*                                                                            *)
  (*   3 1 2 1 3 2                                                               *)
  (*     k=3 starts at 0 -> id 12                                                *)
  (*     k=1 starts at 1 -> id 1                                                 *)
  (*     k=2 starts at 2 -> id 8                                                 *)
  (*                                                                            *)
  (*   2 3 1 2 1 3                                                               *)
  (*     k=3 starts at 1 -> id 13                                                *)
  (*     k=2 starts at 0 -> id 6                                                 *)
  (*     k=1 starts at 2 -> id 2                                                 *)
  (*                                                                            *)
  (* Expected solver output:                                                     *)
  (*   [[12; 1; 8]; [13; 6; 2]]                                                  *)
  (******************************************************************************)

  Definition langford_3_problem : problem CCol CColor CRowId :=
    langford_problem 3.

  Definition langford_3_solutions : list (list CRowId) :=
    solve_ids 10 langford_3_problem.

  Example langford_3_expected :
    langford_3_solutions =
      [[12; 1; 8];
       [13; 6; 2]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* waerden_problem                                                             *)
  (*                                                                            *)
  (* Van der Waerden-style AP-avoiding colorings.                                *)
  (*                                                                            *)
  (* Example:                                                                    *)
  (*   n = 3 positions                                                           *)
  (*   q = 2 colors                                                              *)
  (*   k = 3 arithmetic progression length                                       *)
  (*                                                                            *)
  (* Positions are 0,1,2. The only 3-term arithmetic progression is [0;1;2].      *)
  (* Therefore the bad colorings are exactly:                                    *)
  (*                                                                            *)
  (*   [0;0;0] and [1;1;1]                                                       *)
  (*                                                                            *)
  (* The six good colorings are kept, indexed in generator order:                 *)
  (*                                                                            *)
  (*   id 0 -> [0;0;1]                                                           *)
  (*   id 1 -> [0;1;0]                                                           *)
  (*   id 2 -> [0;1;1]                                                           *)
  (*   id 3 -> [1;0;0]                                                           *)
  (*   id 4 -> [1;0;1]                                                           *)
  (*   id 5 -> [1;1;0]                                                           *)
  (*                                                                            *)
  (* The DLX problem has primary [PickOne], so every valid coloring is returned   *)
  (* as a singleton solution.                                                    *)
  (******************************************************************************)

  Definition waerden_3_2_3_problem : problem CCol CColor CRowId :=
    waerden_problem 3 2 3.

  Definition waerden_3_2_3_solutions : list (list CRowId) :=
    solve_ids 10 waerden_3_2_3_problem.

  Example waerden_3_2_3_expected :
    waerden_3_2_3_solutions =
      [[0]; [1]; [2]; [3]; [4]; [5]].
  Proof.
    vm_compute.
    reflexivity.
  Qed.


  (******************************************************************************)
  (* waerden_problem, unsatisfiable threshold example                            *)
  (*                                                                            *)
  (* For two colors and 3-term arithmetic progressions, length 9 is the classic  *)
  (* threshold: every 2-coloring of 0..8 has a monochromatic 3-term AP.           *)
  (*                                                                            *)
  (* Therefore the generated AP-avoiding coloring universe is empty, and the DLX  *)
  (* solver returns no solutions.                                                *)
  (******************************************************************************)

  Definition waerden_9_2_3_problem : problem CCol CColor CRowId :=
    waerden_problem 9 2 3.

  Definition waerden_9_2_3_solutions : list (list CRowId) :=
    solve_ids 10 waerden_9_2_3_problem.

  Example waerden_9_2_3_expected :
    waerden_9_2_3_solutions = [].
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  (* end hide *)


End CombinatoricsGDanceExamples.

(** ** Public extraction API

    [PublicAPI] contains specialized wrappers intended for OCaml/Melange/React.

    The generic [solve_ids] function is polymorphic and expects equality
    dictionaries.  That shape is convenient in Rocq but awkward from JavaScript.

    The [api_*_ids] functions close over the appropriate equality instances on
    the Rocq side.  JavaScript callers therefore pass only ordinary numeric
    parameters, converted to extracted Rocq naturals by the frontend adapter.

    These wrappers are the intended public extraction roots.
*)

Module PublicAPI.

  Import Core.

  (******************************************************************************)
  (* Specialized solve_ids wrappers                                              *)
  (*                                                                            *)
  (* These close over the Eqb instances on the Rocq side, so JavaScript does not *)
  (* need to pass Eqb dictionaries.                                              *)
  (******************************************************************************)

  Definition solve_ids_combinatorics
    (fuel : nat)
    (p : problem Combinatorics.CCol Combinatorics.CColor Combinatorics.CRowId)
    : list (list Combinatorics.CRowId) :=
    @solve_ids
      Combinatorics.CCol
      Combinatorics.CColor
      Combinatorics.CRowId
      Combinatorics.Eqb_CCol
      Eqb_nat
      fuel
      p.

  Definition solve_ids_sudoku
    (fuel : nat)
    (p : problem SudokuProblem.GCol SudokuProblem.SColor SudokuProblem.SRowId)
    : list (list SudokuProblem.SRowId) :=
    @solve_ids
      SudokuProblem.GCol
      SudokuProblem.SColor
      SudokuProblem.SRowId
      SudokuProblem.Eqb_GCol
      Eqb_nat
      fuel
      p.

  Definition solve_ids_warehouse
    (fuel : nat)
    (p : problem
           Guaranteed_K_Warehouse.WItem
           Guaranteed_K_Warehouse.WColor
           Guaranteed_K_Warehouse.WRowId)
    : list (list Guaranteed_K_Warehouse.WRowId) :=
    @solve_ids
      Guaranteed_K_Warehouse.WItem
      Guaranteed_K_Warehouse.WColor
      Guaranteed_K_Warehouse.WRowId
      Eqb_string
      Eqb_string
      fuel
      p.


  (******************************************************************************)
  (* Convenience endpoint-style wrappers                                         *)
  (*                                                                            *)
  (* These are even easier for React: pass URL params, get solution IDs.         *)
  (******************************************************************************)

  Definition api_nqueens_ids (fuel n : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.nqueens_problem n).

  Definition api_langford_ids (fuel n : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.langford_problem n).

  Definition api_waerden_ids (fuel n q k : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.waerden_problem n q k).

  Definition api_tuple_ids (fuel k n : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.tuple_problem k n).

  Definition api_permutation_ids (fuel k n : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.permutation_problem k n).

  Definition api_combination_ids (fuel k n : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.combination_problem k n).

  Definition api_partition_ids (fuel n : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.partition_problem n).

  Definition api_partition_k_ids (fuel n k : nat) : list (list nat) :=
    solve_ids_combinatorics fuel (Combinatorics.partition_problem_k n k).

  Definition api_set_partition_generated_ids
    (fuel n : nat)
    : list (list nat) :=
    solve_ids_combinatorics fuel
      (Combinatorics.set_partition_problem_generated n).

  Definition api_set_partition_k_generated_ids
    (fuel k n : nat)
    : list (list nat) :=
    solve_ids_combinatorics fuel
      (Combinatorics.set_partition_k_problem_generated k n).

  Definition api_multiset_partition_generated_ids
    (fuel n label_count : nat)
    : list (list nat) :=
    solve_ids_combinatorics fuel
      (Combinatorics.multiset_partition_problem_generated n label_count).

  Definition api_multiset_partition_k_generated_ids
    (fuel k n label_count : nat)
    : list (list nat) :=
    solve_ids_combinatorics fuel
      (Combinatorics.multiset_partition_k_problem_generated k n label_count).

  Definition api_sudoku_exact_ids
    (fuel R C r c : nat)
    : list (list nat) :=
    solve_ids_sudoku fuel
      (SudokuProblem.generalized_sudoku_problem_exact R C r c).

  Definition api_sudoku_at_most_ids
    (fuel R C r c : nat)
    : list (list nat) :=
    solve_ids_sudoku fuel
      (SudokuProblem.generalized_sudoku_problem_at_most R C r c).

  Definition api_warehouse_guaranteed_ids
    (fuel n_items n_sources k : nat)
    : list (list nat) :=
    solve_ids_warehouse fuel
      (Guaranteed_K_Warehouse.guaranteed_k_problem n_items n_sources k).

  Definition api_warehouse_guaranteed_colored_ids
    (fuel n_items n_sources n_product_colors n_source_reqs k : nat)
    : list (list nat) :=
    solve_ids_warehouse fuel
      (Guaranteed_K_Warehouse.guaranteed_k_colored_problem
         n_items n_sources n_product_colors n_source_reqs k).

End PublicAPI.

From Stdlib Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "gdance.ml"
  PublicAPI.api_nqueens_ids
  PublicAPI.api_langford_ids
  PublicAPI.api_waerden_ids
  PublicAPI.api_tuple_ids
  PublicAPI.api_permutation_ids
  PublicAPI.api_combination_ids
  PublicAPI.api_partition_ids
  PublicAPI.api_partition_k_ids
  PublicAPI.api_set_partition_generated_ids
  PublicAPI.api_set_partition_k_generated_ids
  PublicAPI.api_multiset_partition_generated_ids
  PublicAPI.api_multiset_partition_k_generated_ids
  PublicAPI.api_sudoku_exact_ids
  PublicAPI.api_sudoku_at_most_ids
  PublicAPI.api_warehouse_guaranteed_ids
  PublicAPI.api_warehouse_guaranteed_colored_ids
  (* Core.solve 
  Core.solve_ids 
  Core.solution_row_ids 
  SudokuProblem.generalized_sudoku_problem_at_most
  SudokuProblem.generalized_sudoku_problem_exact
  SudokuProblem.generalized_sudoku_problem_at_most_with_givens
  SudokuProblem.generalized_sudoku_problem_exact_with_givens
  SudokuProblem.generated_solution_rows
  SudokuProblem.generated_solution_ids
  Guaranteed_K_Warehouse.guaranteed_k_colored_problem
  Combinatorics.nqueens_problem
  Combinatorics.multiset_partition_k_problem
  Combinatorics.multiset_partition_k_problem_generated
  Combinatorics.multiset_partition_k_problem_counts
  Combinatorics.multiset_partition_problem
  Combinatorics.multiset_partition_problem_generated
  Combinatorics.multiset_partition_problem_counts
  Combinatorics.set_partition_k_problem
  Combinatorics.set_partition_k_problem_generated
  Combinatorics.set_partition_problem
  Combinatorics.set_partition_problem_generated
  Combinatorics.partition_problem_k
  Combinatorics.partition_problem
  Combinatorics.combination_problem
  Combinatorics.permutation_problem
  Combinatorics.tuple_problem
  Combinatorics.langford_problem
  Combinatorics.waerden_problem *)
.