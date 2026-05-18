
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> Nil
| S len0 -> Cons (start, (seq (S start) len0))

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Nil -> None
        | Cons (x, _) -> Some x)
| S n0 -> (match l with
           | Nil -> None
           | Cons (_, l') -> nth_error l' n0)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Nil -> Nil
| Cons (x, l0) -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, l0) -> fold_left f l0 (f a0 b)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> False
| Cons (a, l0) -> (match f a with
                   | True -> True
                   | False -> existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f x with
   | True -> Cons (x, (filter f l0))
   | False -> filter f l0)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Nil -> None
| Cons (x, tl) -> (match f x with
                   | True -> Some x
                   | False -> find f tl)

(** val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec combine l l' =
  match l with
  | Nil -> Nil
  | Cons (x, tl) ->
    (match l' with
     | Nil -> Nil
     | Cons (y, tl') -> Cons ((Pair (x, y)), (combine tl tl')))

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

module GDance =
 struct
  type 'a coq_Eqb =
    'a -> 'a -> bool
    (* singleton inductive, whose constructor was Build_Eqb *)

  (** val eqb : 'a1 coq_Eqb -> 'a1 -> 'a1 -> bool **)

  let eqb eqb2 =
    eqb2

  (** val coq_Eqb_nat : nat coq_Eqb **)

  let coq_Eqb_nat =
    Nat.eqb

  (** val coq_Eqb_string : string coq_Eqb **)

  let coq_Eqb_string =
    eqb1

  type ('item, 'color) citem = { ci_col : 'item; ci_color : 'color option }

  (** val ci_col : ('a1, 'a2) citem -> 'a1 **)

  let ci_col c =
    c.ci_col

  (** val ci_color : ('a1, 'a2) citem -> 'a2 option **)

  let ci_color c =
    c.ci_color

  type ('item, 'color, 'rowId) row = { row_id : 'rowId;
                                       row_items : ('item, 'color) citem list }

  (** val row_id : ('a1, 'a2, 'a3) row -> 'a3 **)

  let row_id r =
    r.row_id

  (** val row_items : ('a1, 'a2, 'a3) row -> ('a1, 'a2) citem list **)

  let row_items r =
    r.row_items

  type ('item, 'color, 'rowId) problem = { primary_items : 'item list;
                                           rows : ('item, 'color, 'rowId) row
                                                  list }

  (** val primary_items : ('a1, 'a2, 'a3) problem -> 'a1 list **)

  let primary_items p =
    p.primary_items

  (** val rows : ('a1, 'a2, 'a3) problem -> ('a1, 'a2, 'a3) row list **)

  let rows p =
    p.rows

  (** val remove_primary : 'a1 coq_Eqb -> 'a1 -> 'a1 list -> 'a1 list **)

  let remove_primary h i ps =
    filter (fun j -> negb (h j i)) ps

  (** val cell_on :
      'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row -> ('a1, 'a2) citem option **)

  let cell_on h i r =
    find (fun ci -> h ci.ci_col i) r.row_items

  (** val row_has_col : 'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row -> bool **)

  let row_has_col h i r =
    match cell_on h i r with
    | Some _ -> True
    | None -> False

  (** val rows_with_col :
      'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row list -> ('a1, 'a2, 'a3) row
      list **)

  let rows_with_col h i rs =
    filter (row_has_col h i) rs

  (** val col_len : 'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) problem -> nat **)

  let col_len h i p =
    length (rows_with_col h i p.rows)

  (** val cover :
      'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) problem -> ('a1, 'a2, 'a3) problem **)

  let cover h i p =
    { primary_items = (remove_primary h i p.primary_items); rows =
      (filter (fun r -> negb (row_has_col h i r)) p.rows) }

  (** val row_color_ok :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) row -> bool **)

  let row_color_ok h h0 i x r =
    match cell_on h i r with
    | Some ci -> (match ci.ci_color with
                  | Some y -> h0 y x
                  | None -> False)
    | None -> True

  (** val purify :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) problem ->
      ('a1, 'a2, 'a3) problem **)

  let purify h h0 i x p =
    { primary_items = p.primary_items; rows =
      (filter (row_color_ok h h0 i x) p.rows) }

  (** val commit_cell :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> ('a1, 'a2) citem -> ('a1, 'a2, 'a3)
      problem -> ('a1, 'a2, 'a3) problem **)

  let commit_cell h h0 ci p =
    match ci.ci_color with
    | Some x -> purify h h0 ci.ci_col x p
    | None -> cover h ci.ci_col p

  (** val commit_other_cell :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> ('a1, 'a2) citem -> ('a1, 'a2,
      'a3) problem -> ('a1, 'a2, 'a3) problem **)

  let commit_other_cell h h0 chosen_col ci p =
    match h ci.ci_col chosen_col with
    | True -> p
    | False -> commit_cell h h0 ci p

  (** val commit :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row -> ('a1, 'a2,
      'a3) problem -> ('a1, 'a2, 'a3) problem **)

  let commit h h0 chosen_col chosen_row p =
    fold_left (fun acc ci -> commit_other_cell h h0 chosen_col ci acc)
      chosen_row.row_items (cover h chosen_col p)

  (** val choose_col_aux :
      'a1 coq_Eqb -> ('a1, 'a2, 'a3) problem -> 'a1 -> nat -> 'a1 list -> 'a1 **)

  let rec choose_col_aux h p best best_len = function
  | Nil -> best
  | Cons (i, rest') ->
    let n = col_len h i p in
    (match Nat.ltb n best_len with
     | True -> choose_col_aux h p i n rest'
     | False -> choose_col_aux h p best best_len rest')

  (** val choose_col :
      'a1 coq_Eqb -> ('a1, 'a2, 'a3) problem -> 'a1 option **)

  let choose_col h p =
    match p.primary_items with
    | Nil -> None
    | Cons (i, rest) -> Some (choose_col_aux h p i (col_len h i p) rest)

  (** val search :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> nat -> ('a1, 'a2, 'a3) problem -> ('a1,
      'a2, 'a3) row list list **)

  let rec search h h0 fuel p =
    match fuel with
    | O -> Nil
    | S fuel' ->
      (match p.primary_items with
       | Nil -> Cons (Nil, Nil)
       | Cons (_, _) ->
         (match choose_col h p with
          | Some c ->
            flat_map (fun r ->
              map (fun sol -> Cons (r, sol))
                (search h h0 fuel' (commit h h0 c r p)))
              (rows_with_col h c p.rows)
          | None -> Cons (Nil, Nil)))

  (** val solve :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> nat -> ('a1, 'a2, 'a3) problem -> ('a1,
      'a2, 'a3) row list list **)

  let solve =
    search

  (** val solution_row_ids : ('a1, 'a2, 'a3) row list -> 'a3 list **)

  let solution_row_ids sol =
    map (fun r -> r.row_id) sol

  (** val solve_ids :
      'a1 coq_Eqb -> 'a2 coq_Eqb -> nat -> ('a1, 'a2, 'a3) problem -> 'a3
      list list **)

  let solve_ids h h0 fuel p =
    map solution_row_ids (solve h h0 fuel p)
 end

module SudokuProblem =
 struct
  type coq_GCol =
  | Cell of nat * nat
  | RowSym of nat * nat
  | ColSym of nat * nat
  | BoxSym of nat * nat * nat

  (** val gcol_eqb : coq_GCol -> coq_GCol -> bool **)

  let gcol_eqb a b =
    match a with
    | Cell (r1, c1) ->
      (match b with
       | Cell (r2, c2) ->
         (match Nat.eqb r1 r2 with
          | True -> Nat.eqb c1 c2
          | False -> False)
       | _ -> False)
    | RowSym (r1, s1) ->
      (match b with
       | RowSym (r2, s2) ->
         (match Nat.eqb r1 r2 with
          | True -> Nat.eqb s1 s2
          | False -> False)
       | _ -> False)
    | ColSym (c1, s1) ->
      (match b with
       | ColSym (c2, s2) ->
         (match Nat.eqb c1 c2 with
          | True -> Nat.eqb s1 s2
          | False -> False)
       | _ -> False)
    | BoxSym (br1, bc1, s1) ->
      (match b with
       | BoxSym (br2, bc2, s2) ->
         (match match Nat.eqb br1 br2 with
                | True -> Nat.eqb bc1 bc2
                | False -> False with
          | True -> Nat.eqb s1 s2
          | False -> False)
       | _ -> False)

  (** val coq_Eqb_GCol : coq_GCol GDance.coq_Eqb **)

  let coq_Eqb_GCol =
    gcol_eqb

  type coq_SColor = nat

  type coq_SRowId = nat

  (** val su : coq_GCol -> (coq_GCol, coq_SColor) GDance.citem **)

  let su x =
    { GDance.ci_col = x; GDance.ci_color = None }

  (** val rows_count : nat -> nat -> nat **)

  let rows_count =
    mul

  (** val cols_count : nat -> nat -> nat **)

  let cols_count =
    mul

  (** val box_size : nat -> nat -> nat **)

  let box_size =
    mul

  (** val max3 : nat -> nat -> nat -> nat **)

  let max3 a b c =
    Nat.max a (Nat.max b c)

  (** val alphabet_size : nat -> nat -> nat -> nat -> nat **)

  let alphabet_size r c r0 c0 =
    max3 (rows_count r r0) (cols_count c c0) (box_size r0 c0)

  (** val row_indices : nat -> nat -> nat list **)

  let row_indices r r0 =
    seq O (rows_count r r0)

  (** val col_indices : nat -> nat -> nat list **)

  let col_indices c c0 =
    seq O (cols_count c c0)

  (** val symbols : nat -> nat -> nat -> nat -> nat list **)

  let symbols r c r0 c0 =
    seq O (alphabet_size r c r0 c0)

  (** val box_row_of : nat -> nat -> nat **)

  let box_row_of r row0 =
    Nat.div row0 r

  (** val box_col_of : nat -> nat -> nat **)

  let box_col_of c col =
    Nat.div col c

  (** val candidate_id :
      nat -> nat -> nat -> nat -> nat -> nat -> nat -> coq_SRowId **)

  let candidate_id r c r0 c0 row0 col sym =
    add
      (mul (add (mul row0 (cols_count c c0)) col) (alphabet_size r c r0 c0))
      sym

  (** val candidate_items :
      nat -> nat -> nat -> nat -> nat -> nat -> nat -> coq_GCol list **)

  let candidate_items _ _ r c row0 col sym =
    Cons ((Cell (row0, col)), (Cons ((RowSym (row0, sym)), (Cons ((ColSym
      (col, sym)), (Cons ((BoxSym ((box_row_of r row0), (box_col_of c col),
      sym)), Nil)))))))

  (** val candidate_row :
      nat -> nat -> nat -> nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor,
      coq_SRowId) GDance.row **)

  let candidate_row r c r0 c0 row_ix col_ix sym =
    { GDance.row_id = (candidate_id r c r0 c0 row_ix col_ix sym);
      GDance.row_items =
      (map su (candidate_items r c r0 c0 row_ix col_ix sym)) }

  (** val all_cells : nat -> nat -> nat -> nat -> coq_GCol list **)

  let all_cells r c r0 c0 =
    flat_map (fun row0 ->
      map (fun col -> Cell (row0, col)) (col_indices c c0)) (row_indices r r0)

  (** val all_row_symbol_constraints :
      nat -> nat -> nat -> nat -> coq_GCol list **)

  let all_row_symbol_constraints r c r0 c0 =
    flat_map (fun row0 ->
      map (fun sym -> RowSym (row0, sym)) (symbols r c r0 c0))
      (row_indices r r0)

  (** val all_col_symbol_constraints :
      nat -> nat -> nat -> nat -> coq_GCol list **)

  let all_col_symbol_constraints r c r0 c0 =
    flat_map (fun col ->
      map (fun sym -> ColSym (col, sym)) (symbols r c r0 c0))
      (col_indices c c0)

  (** val all_box_symbol_constraints :
      nat -> nat -> nat -> nat -> coq_GCol list **)

  let all_box_symbol_constraints r c r0 c0 =
    flat_map (fun br ->
      flat_map (fun bc ->
        map (fun sym -> BoxSym (br, bc, sym)) (symbols r c r0 c0)) (seq O c))
      (seq O r)

  (** val all_sudoku_constraints :
      nat -> nat -> nat -> nat -> coq_GCol list **)

  let all_sudoku_constraints r c r0 c0 =
    app (all_cells r c r0 c0)
      (app (all_row_symbol_constraints r c r0 c0)
        (app (all_col_symbol_constraints r c r0 c0)
          (all_box_symbol_constraints r c r0 c0)))

  (** val all_candidate_rows :
      nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor, coq_SRowId)
      GDance.row list **)

  let all_candidate_rows r c r0 c0 =
    flat_map (fun row0 ->
      flat_map (fun col ->
        map (fun sym -> candidate_row r c r0 c0 row0 col sym)
          (symbols r c r0 c0))
        (col_indices c c0))
      (row_indices r r0)

  (** val generalized_sudoku_problem_at_most :
      nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor, coq_SRowId)
      GDance.problem **)

  let generalized_sudoku_problem_at_most r c r0 c0 =
    { GDance.primary_items = (all_cells r c r0 c0); GDance.rows =
      (all_candidate_rows r c r0 c0) }

  (** val generalized_sudoku_problem_exact :
      nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor, coq_SRowId)
      GDance.problem **)

  let generalized_sudoku_problem_exact r c r0 c0 =
    { GDance.primary_items = (all_sudoku_constraints r c r0 c0);
      GDance.rows = (all_candidate_rows r c r0 c0) }
 end

module Guaranteed_K_Warehouse =
 struct
  (** val ascii_of_digit : nat -> ascii **)

  let ascii_of_digit = function
  | O -> Ascii (False, False, False, False, True, True, False, False)
  | S n ->
    (match n with
     | O -> Ascii (True, False, False, False, True, True, False, False)
     | S n0 ->
       (match n0 with
        | O -> Ascii (False, True, False, False, True, True, False, False)
        | S n1 ->
          (match n1 with
           | O -> Ascii (True, True, False, False, True, True, False, False)
           | S n2 ->
             (match n2 with
              | O ->
                Ascii (False, False, True, False, True, True, False, False)
              | S n3 ->
                (match n3 with
                 | O ->
                   Ascii (True, False, True, False, True, True, False, False)
                 | S n4 ->
                   (match n4 with
                    | O ->
                      Ascii (False, True, True, False, True, True, False,
                        False)
                    | S n5 ->
                      (match n5 with
                       | O ->
                         Ascii (True, True, True, False, True, True, False,
                           False)
                       | S n6 ->
                         (match n6 with
                          | O ->
                            Ascii (False, False, False, True, True, True,
                              False, False)
                          | S _ ->
                            Ascii (True, False, False, True, True, True,
                              False, False)))))))))

  (** val digits_rev_fuel : nat -> nat -> nat list **)

  let rec digits_rev_fuel fuel n =
    match fuel with
    | O -> Nil
    | S fuel' ->
      let d = Nat.modulo n (S (S (S (S (S (S (S (S (S (S O)))))))))) in
      (match Nat.ltb n (S (S (S (S (S (S (S (S (S (S O)))))))))) with
       | True -> Cons (d, Nil)
       | False ->
         Cons (d,
           (digits_rev_fuel fuel'
             (Nat.div n (S (S (S (S (S (S (S (S (S (S O))))))))))))))

  (** val string_of_ascii_list : ascii list -> string **)

  let rec string_of_ascii_list = function
  | Nil -> EmptyString
  | Cons (x, xs') -> String (x, (string_of_ascii_list xs'))

  (** val nat_to_string : nat -> string **)

  let nat_to_string n =
    string_of_ascii_list (map ascii_of_digit (rev (digits_rev_fuel (S n) n)))

  (** val label : string -> nat -> string **)

  let label prefix i =
    append prefix (nat_to_string (S i))

  (** val generated_names : string -> nat -> string list **)

  let generated_names prefix n =
    map (label prefix) (seq O n)

  (** val indexed : 'a1 list -> (nat, 'a1) prod list **)

  let indexed xs =
    combine (seq O (length xs)) xs

  (** val nth_option : 'a1 list -> nat -> 'a1 option **)

  let nth_option =
    nth_error

  (** val choose_color : string list -> nat -> string option **)

  let choose_color colors i =
    match length colors with
    | O -> None
    | S n -> nth_option colors (Nat.modulo i (S n))

  type coq_WItem = string

  type coq_WColor = string

  type coq_WRowId = nat

  (** val primary_item_citem :
      string -> (coq_WItem, coq_WColor) GDance.citem **)

  let primary_item_citem item0 =
    { GDance.ci_col = item0; GDance.ci_color = None }

  (** val secondary_source_citem :
      string -> string option -> (coq_WItem, coq_WColor) GDance.citem **)

  let secondary_source_citem src source_color =
    { GDance.ci_col = src; GDance.ci_color = source_color }

  (** val warehouse_row :
      coq_WRowId -> string -> string list -> string option -> string option
      -> (coq_WItem, coq_WColor, coq_WRowId) GDance.row **)

  let warehouse_row id src items _ source_color =
    { GDance.row_id = id; GDance.row_items =
      (app (map primary_item_citem items) (Cons
        ((secondary_source_citem src source_color), Nil))) }

  (** val assigned_items_for_source_shifted :
      string list -> nat -> nat -> nat -> string list **)

  let assigned_items_for_source_shifted items n_sources witness_id source_id =
    map snd
      (filter (fun pat ->
        let Pair (ii, _) = pat in
        Nat.eqb (Nat.modulo (add ii witness_id) n_sources) source_id)
        (indexed items))

  (** val guaranteed_row_id : nat -> nat -> nat -> coq_WRowId **)

  let guaranteed_row_id n_sources witness_id source_id =
    add (mul witness_id n_sources) source_id

  (** val guaranteed_rows_for_witness :
      string list -> string list -> nat -> (coq_WItem, coq_WColor,
      coq_WRowId) GDance.row list **)

  let guaranteed_rows_for_witness items sources witness_id =
    map (fun pat ->
      let Pair (si, src) = pat in
      warehouse_row (guaranteed_row_id (length sources) witness_id si) src
        (assigned_items_for_source_shifted items (length sources) witness_id
          si)
        None None)
      (indexed sources)

  (** val guaranteed_k_rows :
      string list -> string list -> nat -> (coq_WItem, coq_WColor,
      coq_WRowId) GDance.row list **)

  let guaranteed_k_rows items sources k =
    flat_map (fun witness_id ->
      guaranteed_rows_for_witness items sources witness_id) (seq O k)

  (** val guaranteed_k_problem :
      nat -> nat -> nat -> (coq_WItem, coq_WColor, coq_WRowId) GDance.problem **)

  let guaranteed_k_problem n_items n_sources k =
    let items =
      generated_names (String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), (String ((Ascii (True, False, True, True,
        False, True, True, False)), EmptyString)))))))) n_items
    in
    let sources =
      generated_names (String ((Ascii (True, True, False, False, True, True,
        True, False)), (String ((Ascii (False, True, False, False, True,
        True, True, False)), (String ((Ascii (True, True, False, False,
        False, True, True, False)), EmptyString)))))) n_sources
    in
    { GDance.primary_items = items; GDance.rows =
    (guaranteed_k_rows items sources k) }

  (** val guaranteed_rows_for_witness_colored :
      string list -> string list -> string list -> string list -> nat ->
      (coq_WItem, coq_WColor, coq_WRowId) GDance.row list **)

  let guaranteed_rows_for_witness_colored items sources product_colors source_reqs witness_id =
    map (fun pat ->
      let Pair (si, src) = pat in
      let product_color = choose_color product_colors (add witness_id si) in
      let source_color = choose_color source_reqs si in
      warehouse_row (guaranteed_row_id (length sources) witness_id si) src
        (assigned_items_for_source_shifted items (length sources) witness_id
          si)
        product_color source_color)
      (indexed sources)

  (** val guaranteed_k_colored_rows :
      string list -> string list -> string list -> string list -> nat ->
      (coq_WItem, coq_WColor, coq_WRowId) GDance.row list **)

  let guaranteed_k_colored_rows items sources product_colors source_reqs k =
    flat_map (fun witness_id ->
      guaranteed_rows_for_witness_colored items sources product_colors
        source_reqs witness_id)
      (seq O k)

  (** val guaranteed_k_colored_problem :
      nat -> nat -> nat -> nat -> nat -> (coq_WItem, coq_WColor, coq_WRowId)
      GDance.problem **)

  let guaranteed_k_colored_problem n_items n_sources n_product_colors n_source_reqs k =
    let items =
      generated_names (String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), (String ((Ascii (True, False, True, True,
        False, True, True, False)), EmptyString)))))))) n_items
    in
    let sources =
      generated_names (String ((Ascii (True, True, False, False, True, True,
        True, False)), (String ((Ascii (False, True, False, False, True,
        True, True, False)), (String ((Ascii (True, True, False, False,
        False, True, True, False)), EmptyString)))))) n_sources
    in
    let product_colors =
      generated_names (String ((Ascii (True, True, False, False, False, True,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, False, True, True, False,
        True, True, False)), (String ((Ascii (True, True, True, True, False,
        True, True, False)), (String ((Ascii (False, True, False, False,
        True, True, True, False)), EmptyString)))))))))) n_product_colors
    in
    let source_reqs =
      generated_names (String ((Ascii (False, True, False, False, True, True,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, False, False, False,
        True, True, True, False)), EmptyString)))))) n_source_reqs
    in
    { GDance.primary_items = items; GDance.rows =
    (guaranteed_k_colored_rows items sources product_colors source_reqs k) }
 end

module Combinatorics =
 struct
  type coq_CCol =
  | Slot of nat
  | Value of nat
  | Occur of nat
  | PickOne
  | PartAt of nat * nat
  | QRow of nat
  | QCol of nat
  | QDiag1 of nat
  | QDiag2 of nat

  (** val ccol_eqb : coq_CCol -> coq_CCol -> bool **)

  let ccol_eqb a b =
    match a with
    | Slot i -> (match b with
                 | Slot j -> Nat.eqb i j
                 | _ -> False)
    | Value i -> (match b with
                  | Value j -> Nat.eqb i j
                  | _ -> False)
    | Occur i -> (match b with
                  | Occur j -> Nat.eqb i j
                  | _ -> False)
    | PickOne -> (match b with
                  | PickOne -> True
                  | _ -> False)
    | PartAt (i, x) ->
      (match b with
       | PartAt (j, y) ->
         (match Nat.eqb i j with
          | True -> Nat.eqb x y
          | False -> False)
       | _ -> False)
    | QRow i -> (match b with
                 | QRow j -> Nat.eqb i j
                 | _ -> False)
    | QCol i -> (match b with
                 | QCol j -> Nat.eqb i j
                 | _ -> False)
    | QDiag1 i -> (match b with
                   | QDiag1 j -> Nat.eqb i j
                   | _ -> False)
    | QDiag2 i -> (match b with
                   | QDiag2 j -> Nat.eqb i j
                   | _ -> False)

  (** val coq_Eqb_CCol : coq_CCol GDance.coq_Eqb **)

  let coq_Eqb_CCol =
    ccol_eqb

  type coq_CColor = nat

  type coq_CRowId = nat

  (** val item : coq_CCol -> (coq_CCol, coq_CColor) GDance.citem **)

  let item c =
    { GDance.ci_col = c; GDance.ci_color = None }

  (** val make_row :
      coq_CRowId -> coq_CCol list -> (coq_CCol, coq_CColor, coq_CRowId)
      GDance.row **)

  let make_row id cols =
    { GDance.row_id = id; GDance.row_items = (map item cols) }

  (** val make_problem :
      coq_CCol list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list ->
      (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let make_problem primary rows0 =
    { GDance.primary_items = primary; GDance.rows = rows0 }

  (** val slots : nat -> coq_CCol list **)

  let slots k =
    map (fun x -> Slot x) (seq O k)

  (** val occurs : nat -> coq_CCol list **)

  let occurs n =
    map (fun x -> Occur x) (seq O n)

  (** val assignment_id : nat -> nat -> nat -> coq_CRowId **)

  let assignment_id n slot value =
    add (mul slot n) value

  (** val tuple_row :
      nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let tuple_row n slot value =
    make_row (assignment_id n slot value) (Cons ((Slot slot), Nil))

  (** val assignment_rows_tuple :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let assignment_rows_tuple k n =
    flat_map (fun s -> map (fun v -> tuple_row n s v) (seq O n)) (seq O k)

  (** val tuple_problem :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let tuple_problem k n =
    make_problem (slots k) (assignment_rows_tuple k n)

  (** val permutation_row :
      nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let permutation_row n slot value =
    make_row (assignment_id n slot value) (Cons ((Slot slot), (Cons ((Value
      value), Nil))))

  (** val assignment_rows_permutation :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let assignment_rows_permutation k n =
    flat_map (fun s -> map (fun v -> permutation_row n s v) (seq O n))
      (seq O k)

  (** val permutation_problem :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let permutation_problem k n =
    make_problem (slots k) (assignment_rows_permutation k n)

  (** val combinations_from : nat -> nat -> nat -> nat list list **)

  let rec combinations_from k start n =
    match k with
    | O -> Cons (Nil, Nil)
    | S k' ->
      flat_map (fun v ->
        map (fun rest -> Cons (v, rest)) (combinations_from k' (S v) n))
        (seq start (sub n start))

  (** val combinations : nat -> nat -> nat list list **)

  let combinations k n =
    combinations_from k O n

  (** val combination_cols_aux : nat -> nat list -> coq_CCol list **)

  let rec combination_cols_aux slot = function
  | Nil -> Nil
  | Cons (x, xs') ->
    Cons ((Slot slot), (Cons ((Value x),
      (combination_cols_aux (S slot) xs'))))

  (** val combination_row :
      coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let combination_row id xs =
    make_row id (Cons (PickOne, (combination_cols_aux O xs)))

  (** val indexed : 'a1 list -> (nat, 'a1) prod list **)

  let indexed xs =
    combine (seq O (length xs)) xs

  (** val combination_problem :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let combination_problem k n =
    make_problem (Cons (PickOne, Nil))
      (map (fun pat -> let Pair (id, xs) = pat in combination_row id xs)
        (indexed (combinations k n)))

  (** val sum_nat : nat list -> nat **)

  let rec sum_nat = function
  | Nil -> O
  | Cons (x, xs') -> add x (sum_nat xs')

  (** val nonincreasing_from : nat -> nat list -> bool **)

  let rec nonincreasing_from prev = function
  | Nil -> True
  | Cons (x, xs') ->
    (match Nat.leb x prev with
     | True -> nonincreasing_from x xs'
     | False -> False)

  (** val nonincreasing : nat list -> bool **)

  let nonincreasing = function
  | Nil -> True
  | Cons (x, xs') -> nonincreasing_from x xs'

  (** val is_partition_of : nat -> nat list -> bool **)

  let is_partition_of n xs =
    match Nat.eqb (sum_nat xs) n with
    | True -> nonincreasing xs
    | False -> False

  (** val partitions_bounded : nat -> nat -> nat -> nat list list **)

  let rec partitions_bounded fuel n max_part =
    match fuel with
    | O -> Nil
    | S fuel' ->
      (match n with
       | O -> Cons (Nil, Nil)
       | S _ ->
         flat_map (fun x ->
           map (fun rest -> Cons (x, rest))
             (partitions_bounded fuel' (sub n x) x))
           (seq (S O) max_part))

  (** val partitions_of : nat -> nat list list **)

  let partitions_of n =
    filter (is_partition_of n) (partitions_bounded (S n) n n)

  (** val partition_cols_aux : nat -> nat list -> coq_CCol list **)

  let rec partition_cols_aux i = function
  | Nil -> Nil
  | Cons (x, xs') -> Cons ((PartAt (i, x)), (partition_cols_aux (S i) xs'))

  (** val partition_row :
      coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let partition_row id xs =
    make_row id (Cons (PickOne, (partition_cols_aux O xs)))

  (** val partition_problem :
      nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let partition_problem n =
    make_problem (Cons (PickOne, Nil))
      (map (fun pat -> let Pair (id, xs) = pat in partition_row id xs)
        (indexed (partitions_of n)))

  (** val has_k_parts : nat -> nat list -> bool **)

  let has_k_parts k xs =
    Nat.eqb (length xs) k

  (** val is_partition_of_k : nat -> nat -> nat list -> bool **)

  let is_partition_of_k n k xs =
    match is_partition_of n xs with
    | True -> has_k_parts k xs
    | False -> False

  (** val partitions_of_k : nat -> nat -> nat list list **)

  let partitions_of_k n k =
    filter (is_partition_of_k n k) (partitions_bounded (S n) n n)

  (** val partition_problem_k :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let partition_problem_k n k =
    make_problem (Cons (PickOne, Nil))
      (map (fun pat -> let Pair (id, xs) = pat in partition_row id xs)
        (indexed (partitions_of_k n k)))

  (** val subsets : nat list -> nat list list **)

  let rec subsets = function
  | Nil -> Cons (Nil, Nil)
  | Cons (x, xs') ->
    let ss = subsets xs' in app ss (map (fun s -> Cons (x, s)) ss)

  (** val nonempty_subsets : nat list -> nat list list **)

  let nonempty_subsets xs =
    filter (fun s -> negb (Nat.eqb (length s) O)) (subsets xs)

  (** val set_partition_row :
      coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let set_partition_row id xs =
    make_row id (map (fun x -> Value x) xs)

  (** val generated_set : nat -> nat list **)

  let generated_set n =
    seq O n

  (** val set_partition_problem_values :
      nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let set_partition_problem_values elems =
    make_problem (map (fun x -> Value x) elems)
      (map (fun pat -> let Pair (id, xs) = pat in set_partition_row id xs)
        (indexed (nonempty_subsets elems)))

  (** val set_partition_problem_generated :
      nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let set_partition_problem_generated n =
    set_partition_problem_values (generated_set n)

  (** val set_partition_k_row :
      nat -> nat -> nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId)
      GDance.row **)

  let set_partition_k_row n slot block_id xs =
    make_row (add (mul slot (Nat.pow (S (S O)) n)) block_id) (Cons ((Slot
      slot), (map (fun x -> Value x) xs)))

  (** val set_partition_k_rows_values :
      nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let set_partition_k_rows_values k elems =
    let n = length elems in
    let blocks = indexed (nonempty_subsets elems) in
    flat_map (fun s ->
      map (fun pat ->
        let Pair (bid, b) = pat in set_partition_k_row n s bid b) blocks)
      (seq O k)

  (** val set_partition_k_problem_values :
      nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let set_partition_k_problem_values k elems =
    make_problem (app (slots k) (map (fun x -> Value x) elems))
      (set_partition_k_rows_values k elems)

  (** val set_partition_k_problem_generated :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let set_partition_k_problem_generated k n =
    set_partition_k_problem_values k (generated_set n)

  (** val multiset_partition_row :
      coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let multiset_partition_row id xs =
    make_row id (map (fun x -> Occur x) xs)

  (** val generated_multiset : nat -> nat -> nat list **)

  let generated_multiset n label_count = match label_count with
  | O -> Nil
  | S _ -> map (fun i -> Nat.modulo i label_count) (seq O n)

  (** val multiset_partition_problem :
      nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let multiset_partition_problem values0 =
    let n = length values0 in
    let occs = seq O n in
    make_problem (occurs n)
      (map (fun pat ->
        let Pair (id, xs) = pat in multiset_partition_row id xs)
        (indexed (nonempty_subsets occs)))

  (** val multiset_partition_problem_generated :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let multiset_partition_problem_generated n label_count =
    multiset_partition_problem (generated_multiset n label_count)

  (** val multiset_partition_k_row :
      nat -> nat -> nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId)
      GDance.row **)

  let multiset_partition_k_row n slot block_id xs =
    make_row (add (mul slot (Nat.pow (S (S O)) n)) block_id) (Cons ((Slot
      slot), (map (fun x -> Occur x) xs)))

  (** val multiset_partition_k_rows :
      nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let multiset_partition_k_rows k values0 =
    let n = length values0 in
    let occs = seq O n in
    let blocks = indexed (nonempty_subsets occs) in
    flat_map (fun s ->
      map (fun pat ->
        let Pair (bid, b) = pat in multiset_partition_k_row n s bid b) blocks)
      (seq O k)

  (** val multiset_partition_k_problem :
      nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let multiset_partition_k_problem k values0 =
    let n = length values0 in
    make_problem (app (slots k) (occurs n))
      (multiset_partition_k_rows k values0)

  (** val multiset_partition_k_problem_generated :
      nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let multiset_partition_k_problem_generated k n label_count =
    multiset_partition_k_problem k (generated_multiset n label_count)

  (** val diag1 : nat -> nat -> nat **)

  let diag1 =
    add

  (** val diag2 : nat -> nat -> nat -> nat **)

  let diag2 n r c =
    add r (sub (sub n (S O)) c)

  (** val queen_id : nat -> nat -> nat -> coq_CRowId **)

  let queen_id n r c =
    add (mul r n) c

  (** val queen_row :
      nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let queen_row n r c =
    make_row (queen_id n r c) (Cons ((QRow r), (Cons ((QCol c), (Cons
      ((QDiag1 (diag1 r c)), (Cons ((QDiag2 (diag2 n r c)), Nil))))))))

  (** val queen_rows :
      nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let queen_rows n =
    flat_map (fun r -> map (fun c -> queen_row n r c) (seq O n)) (seq O n)

  (** val qrows : nat -> coq_CCol list **)

  let qrows n =
    map (fun x -> QRow x) (seq O n)

  (** val qcols : nat -> coq_CCol list **)

  let qcols n =
    map (fun x -> QCol x) (seq O n)

  (** val nqueens_problem :
      nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let nqueens_problem n =
    make_problem (app (qrows n) (qcols n)) (queen_rows n)

  (** val langford_slots : nat -> coq_CCol list **)

  let langford_slots n =
    map (fun x -> Slot x) (seq O (mul (S (S O)) n))

  (** val langford_values : nat -> coq_CCol list **)

  let langford_values n =
    map (fun x -> Value x) (seq (S O) n)

  (** val langford_row_id : nat -> nat -> nat -> coq_CRowId **)

  let langford_row_id n k start =
    add (mul (sub k (S O)) (mul (S (S O)) n)) start

  (** val langford_second_pos : nat -> nat -> nat **)

  let langford_second_pos k start =
    add (add start k) (S O)

  (** val langford_start_count : nat -> nat -> nat **)

  let langford_start_count n k =
    sub (sub (mul (S (S O)) n) k) (S O)

  (** val langford_row :
      nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let langford_row n k start =
    make_row (langford_row_id n k start) (Cons ((Slot start), (Cons ((Slot
      (langford_second_pos k start)), (Cons ((Value k), Nil))))))

  (** val langford_rows_for_value :
      nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let langford_rows_for_value n k =
    map (fun start -> langford_row n k start)
      (seq O (langford_start_count n k))

  (** val langford_rows :
      nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let langford_rows n =
    flat_map (fun k -> langford_rows_for_value n k) (seq (S O) n)

  (** val langford_problem :
      nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let langford_problem n =
    make_problem (app (langford_slots n) (langford_values n))
      (langford_rows n)

  (** val colorings : nat -> nat -> nat list list **)

  let rec colorings n q =
    match n with
    | O -> Cons (Nil, Nil)
    | S n' ->
      flat_map (fun color ->
        map (fun rest -> Cons (color, rest)) (colorings n' q)) (seq O q)

  (** val progression : nat -> nat -> nat -> nat list **)

  let progression start step k =
    map (fun t -> add start (mul t step)) (seq O k)

  (** val progression_in_bounds : nat -> nat -> nat -> nat -> bool **)

  let progression_in_bounds n start step k =
    Nat.ltb (add start (mul (sub k (S O)) step)) n

  (** val arithmetic_progressions : nat -> nat -> nat list list **)

  let arithmetic_progressions n k =
    flat_map (fun start ->
      map (fun step -> progression start step k)
        (filter (fun step -> progression_in_bounds n start step k)
          (seq (S O) n)))
      (seq O n)

  (** val color_at : nat list -> nat -> nat option **)

  let color_at =
    nth_error

  (** val same_color_at : nat list -> nat -> nat -> bool **)

  let same_color_at colors color pos =
    match color_at colors pos with
    | Some c -> Nat.eqb c color
    | None -> False

  (** val monochromatic_progression : nat list -> nat list -> bool **)

  let monochromatic_progression colors = function
  | Nil -> False
  | Cons (pos, rest) ->
    (match color_at colors pos with
     | Some color -> forallb (same_color_at colors color) rest
     | None -> False)

  (** val has_monochromatic_progression :
      nat -> nat -> nat -> nat list -> bool **)

  let has_monochromatic_progression n _ k colors =
    existsb (monochromatic_progression colors) (arithmetic_progressions n k)

  (** val waerden_good_coloring : nat -> nat -> nat -> nat list -> bool **)

  let waerden_good_coloring n q k colors =
    negb (has_monochromatic_progression n q k colors)

  (** val waerden_good_colorings : nat -> nat -> nat -> nat list list **)

  let waerden_good_colorings n q k =
    filter (waerden_good_coloring n q k) (colorings n q)

  (** val coloring_cols_aux : nat -> nat list -> coq_CCol list **)

  let rec coloring_cols_aux pos = function
  | Nil -> Nil
  | Cons (color, colors') ->
    Cons ((PartAt (pos, color)), (coloring_cols_aux (S pos) colors'))

  (** val waerden_coloring_row :
      coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row **)

  let waerden_coloring_row id colors =
    make_row id (Cons (PickOne, (coloring_cols_aux O colors)))

  (** val waerden_rows :
      nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.row list **)

  let waerden_rows n q k =
    map (fun pat ->
      let Pair (id, colors) = pat in waerden_coloring_row id colors)
      (indexed (waerden_good_colorings n q k))

  (** val waerden_problem :
      nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) GDance.problem **)

  let waerden_problem n q k =
    make_problem (Cons (PickOne, Nil)) (waerden_rows n q k)
 end

module PublicAPI =
 struct
  (** val solve_ids_combinatorics :
      nat -> (Combinatorics.coq_CCol, Combinatorics.coq_CColor,
      Combinatorics.coq_CRowId) GDance.problem -> Combinatorics.coq_CRowId
      list list **)

  let solve_ids_combinatorics fuel p =
    GDance.solve_ids Combinatorics.coq_Eqb_CCol GDance.coq_Eqb_nat fuel p

  (** val solve_ids_sudoku :
      nat -> (SudokuProblem.coq_GCol, SudokuProblem.coq_SColor,
      SudokuProblem.coq_SRowId) GDance.problem -> SudokuProblem.coq_SRowId
      list list **)

  let solve_ids_sudoku fuel p =
    GDance.solve_ids SudokuProblem.coq_Eqb_GCol GDance.coq_Eqb_nat fuel p

  (** val solve_ids_warehouse :
      nat -> (Guaranteed_K_Warehouse.coq_WItem,
      Guaranteed_K_Warehouse.coq_WColor, Guaranteed_K_Warehouse.coq_WRowId)
      GDance.problem -> Guaranteed_K_Warehouse.coq_WRowId list list **)

  let solve_ids_warehouse fuel p =
    GDance.solve_ids GDance.coq_Eqb_string GDance.coq_Eqb_string fuel p

  (** val api_nqueens_ids : nat -> nat -> nat list list **)

  let api_nqueens_ids fuel n =
    solve_ids_combinatorics fuel (Combinatorics.nqueens_problem n)

  (** val api_langford_ids : nat -> nat -> nat list list **)

  let api_langford_ids fuel n =
    solve_ids_combinatorics fuel (Combinatorics.langford_problem n)

  (** val api_waerden_ids : nat -> nat -> nat -> nat -> nat list list **)

  let api_waerden_ids fuel n q k =
    solve_ids_combinatorics fuel (Combinatorics.waerden_problem n q k)

  (** val api_tuple_ids : nat -> nat -> nat -> nat list list **)

  let api_tuple_ids fuel k n =
    solve_ids_combinatorics fuel (Combinatorics.tuple_problem k n)

  (** val api_permutation_ids : nat -> nat -> nat -> nat list list **)

  let api_permutation_ids fuel k n =
    solve_ids_combinatorics fuel (Combinatorics.permutation_problem k n)

  (** val api_combination_ids : nat -> nat -> nat -> nat list list **)

  let api_combination_ids fuel k n =
    solve_ids_combinatorics fuel (Combinatorics.combination_problem k n)

  (** val api_partition_ids : nat -> nat -> nat list list **)

  let api_partition_ids fuel n =
    solve_ids_combinatorics fuel (Combinatorics.partition_problem n)

  (** val api_partition_k_ids : nat -> nat -> nat -> nat list list **)

  let api_partition_k_ids fuel n k =
    solve_ids_combinatorics fuel (Combinatorics.partition_problem_k n k)

  (** val api_set_partition_generated_ids : nat -> nat -> nat list list **)

  let api_set_partition_generated_ids fuel n =
    solve_ids_combinatorics fuel
      (Combinatorics.set_partition_problem_generated n)

  (** val api_set_partition_k_generated_ids :
      nat -> nat -> nat -> nat list list **)

  let api_set_partition_k_generated_ids fuel k n =
    solve_ids_combinatorics fuel
      (Combinatorics.set_partition_k_problem_generated k n)

  (** val api_multiset_partition_generated_ids :
      nat -> nat -> nat -> nat list list **)

  let api_multiset_partition_generated_ids fuel n label_count =
    solve_ids_combinatorics fuel
      (Combinatorics.multiset_partition_problem_generated n label_count)

  (** val api_multiset_partition_k_generated_ids :
      nat -> nat -> nat -> nat -> nat list list **)

  let api_multiset_partition_k_generated_ids fuel k n label_count =
    solve_ids_combinatorics fuel
      (Combinatorics.multiset_partition_k_problem_generated k n label_count)

  (** val api_sudoku_exact_ids :
      nat -> nat -> nat -> nat -> nat -> nat list list **)

  let api_sudoku_exact_ids fuel r c r0 c0 =
    solve_ids_sudoku fuel
      (SudokuProblem.generalized_sudoku_problem_exact r c r0 c0)

  (** val api_sudoku_at_most_ids :
      nat -> nat -> nat -> nat -> nat -> nat list list **)

  let api_sudoku_at_most_ids fuel r c r0 c0 =
    solve_ids_sudoku fuel
      (SudokuProblem.generalized_sudoku_problem_at_most r c r0 c0)

  (** val api_warehouse_guaranteed_ids :
      nat -> nat -> nat -> nat -> nat list list **)

  let api_warehouse_guaranteed_ids fuel n_items n_sources k =
    solve_ids_warehouse fuel
      (Guaranteed_K_Warehouse.guaranteed_k_problem n_items n_sources k)

  (** val api_warehouse_guaranteed_colored_ids :
      nat -> nat -> nat -> nat -> nat -> nat -> nat list list **)

  let api_warehouse_guaranteed_colored_ids fuel n_items n_sources n_product_colors n_source_reqs k =
    solve_ids_warehouse fuel
      (Guaranteed_K_Warehouse.guaranteed_k_colored_problem n_items n_sources
        n_product_colors n_source_reqs k)
 end
