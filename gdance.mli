
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val max : nat -> nat -> nat

  val pow : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : nat -> nat -> nat list

val nth_error : 'a1 list -> nat -> 'a1 option

val rev : 'a1 list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

val append : string -> string -> string

module Core :
 sig
  type 'a coq_Eqb =
    'a -> 'a -> bool
    (* singleton inductive, whose constructor was Build_Eqb *)

  val eqb : 'a1 coq_Eqb -> 'a1 -> 'a1 -> bool

  val coq_Eqb_nat : nat coq_Eqb

  val coq_Eqb_string : string coq_Eqb

  type ('item, 'color) citem = { ci_col : 'item; ci_color : 'color option }

  val ci_col : ('a1, 'a2) citem -> 'a1

  val ci_color : ('a1, 'a2) citem -> 'a2 option

  type ('item, 'color, 'rowId) row = { row_id : 'rowId;
                                       row_items : ('item, 'color) citem list }

  val row_id : ('a1, 'a2, 'a3) row -> 'a3

  val row_items : ('a1, 'a2, 'a3) row -> ('a1, 'a2) citem list

  type ('item, 'color, 'rowId) problem = { primary_items : 'item list;
                                           rows : ('item, 'color, 'rowId) row
                                                  list }

  val primary_items : ('a1, 'a2, 'a3) problem -> 'a1 list

  val rows : ('a1, 'a2, 'a3) problem -> ('a1, 'a2, 'a3) row list

  val remove_primary : 'a1 coq_Eqb -> 'a1 -> 'a1 list -> 'a1 list

  val cell_on :
    'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row -> ('a1, 'a2) citem option

  val row_has_col : 'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row -> bool

  val rows_with_col :
    'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row list -> ('a1, 'a2, 'a3) row list

  val col_len : 'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) problem -> nat

  val cover :
    'a1 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) problem -> ('a1, 'a2, 'a3) problem

  val row_color_ok :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) row -> bool

  val purify :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) problem ->
    ('a1, 'a2, 'a3) problem

  val commit_cell :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> ('a1, 'a2) citem -> ('a1, 'a2, 'a3) problem
    -> ('a1, 'a2, 'a3) problem

  val commit_other_cell :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> ('a1, 'a2) citem -> ('a1, 'a2, 'a3)
    problem -> ('a1, 'a2, 'a3) problem

  val commit :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> 'a1 -> ('a1, 'a2, 'a3) row -> ('a1, 'a2,
    'a3) problem -> ('a1, 'a2, 'a3) problem

  val choose_col_aux :
    'a1 coq_Eqb -> ('a1, 'a2, 'a3) problem -> 'a1 -> nat -> 'a1 list -> 'a1

  val choose_col : 'a1 coq_Eqb -> ('a1, 'a2, 'a3) problem -> 'a1 option

  val search :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> nat -> ('a1, 'a2, 'a3) problem -> ('a1,
    'a2, 'a3) row list list

  val solve :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> nat -> ('a1, 'a2, 'a3) problem -> ('a1,
    'a2, 'a3) row list list

  val solution_row_ids : ('a1, 'a2, 'a3) row list -> 'a3 list

  val solve_ids :
    'a1 coq_Eqb -> 'a2 coq_Eqb -> nat -> ('a1, 'a2, 'a3) problem -> 'a3 list
    list
 end

module SudokuProblem :
 sig
  type coq_GCol =
  | Cell of nat * nat
  | RowSym of nat * nat
  | ColSym of nat * nat
  | BoxSym of nat * nat * nat

  val gcol_eqb : coq_GCol -> coq_GCol -> bool

  val coq_Eqb_GCol : coq_GCol Core.coq_Eqb

  type coq_SColor = nat

  type coq_SRowId = nat

  val su : coq_GCol -> (coq_GCol, coq_SColor) Core.citem

  val rows_count : nat -> nat -> nat

  val cols_count : nat -> nat -> nat

  val box_size : nat -> nat -> nat

  val max3 : nat -> nat -> nat -> nat

  val alphabet_size : nat -> nat -> nat -> nat -> nat

  val row_indices : nat -> nat -> nat list

  val col_indices : nat -> nat -> nat list

  val symbols : nat -> nat -> nat -> nat -> nat list

  val box_row_of : nat -> nat -> nat

  val box_col_of : nat -> nat -> nat

  val candidate_id :
    nat -> nat -> nat -> nat -> nat -> nat -> nat -> coq_SRowId

  val candidate_items :
    nat -> nat -> nat -> nat -> nat -> nat -> nat -> coq_GCol list

  val candidate_row :
    nat -> nat -> nat -> nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor,
    coq_SRowId) Core.row

  val all_cells : nat -> nat -> nat -> nat -> coq_GCol list

  val all_row_symbol_constraints : nat -> nat -> nat -> nat -> coq_GCol list

  val all_col_symbol_constraints : nat -> nat -> nat -> nat -> coq_GCol list

  val all_box_symbol_constraints : nat -> nat -> nat -> nat -> coq_GCol list

  val all_sudoku_constraints : nat -> nat -> nat -> nat -> coq_GCol list

  val all_candidate_rows :
    nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor, coq_SRowId) Core.row
    list

  val generalized_sudoku_problem_at_most :
    nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor, coq_SRowId)
    Core.problem

  val generalized_sudoku_problem_exact :
    nat -> nat -> nat -> nat -> (coq_GCol, coq_SColor, coq_SRowId)
    Core.problem
 end

module Guaranteed_K_Warehouse :
 sig
  val ascii_of_digit : nat -> ascii

  val digits_rev_fuel : nat -> nat -> nat list

  val string_of_ascii_list : ascii list -> string

  val nat_to_string : nat -> string

  val label : string -> nat -> string

  val generated_names : string -> nat -> string list

  val indexed : 'a1 list -> (nat, 'a1) prod list

  val nth_option : 'a1 list -> nat -> 'a1 option

  val choose_color : string list -> nat -> string option

  type coq_WItem = string

  type coq_WColor = string

  type coq_WRowId = nat

  val primary_item_citem : string -> (coq_WItem, coq_WColor) Core.citem

  val secondary_source_citem :
    string -> string option -> (coq_WItem, coq_WColor) Core.citem

  val warehouse_row :
    coq_WRowId -> string -> string list -> string option -> string option ->
    (coq_WItem, coq_WColor, coq_WRowId) Core.row

  val assigned_items_for_source_shifted :
    string list -> nat -> nat -> nat -> string list

  val guaranteed_row_id : nat -> nat -> nat -> coq_WRowId

  val guaranteed_rows_for_witness :
    string list -> string list -> nat -> (coq_WItem, coq_WColor, coq_WRowId)
    Core.row list

  val guaranteed_k_rows :
    string list -> string list -> nat -> (coq_WItem, coq_WColor, coq_WRowId)
    Core.row list

  val guaranteed_k_problem :
    nat -> nat -> nat -> (coq_WItem, coq_WColor, coq_WRowId) Core.problem

  val guaranteed_rows_for_witness_colored :
    string list -> string list -> string list -> string list -> nat ->
    (coq_WItem, coq_WColor, coq_WRowId) Core.row list

  val guaranteed_k_colored_rows :
    string list -> string list -> string list -> string list -> nat ->
    (coq_WItem, coq_WColor, coq_WRowId) Core.row list

  val guaranteed_k_colored_problem :
    nat -> nat -> nat -> nat -> nat -> (coq_WItem, coq_WColor, coq_WRowId)
    Core.problem
 end

module Combinatorics :
 sig
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

  val ccol_eqb : coq_CCol -> coq_CCol -> bool

  val coq_Eqb_CCol : coq_CCol Core.coq_Eqb

  type coq_CColor = nat

  type coq_CRowId = nat

  val item : coq_CCol -> (coq_CCol, coq_CColor) Core.citem

  val make_row :
    coq_CRowId -> coq_CCol list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val make_problem :
    coq_CCol list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list ->
    (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val slots : nat -> coq_CCol list

  val occurs : nat -> coq_CCol list

  val assignment_id : nat -> nat -> nat -> coq_CRowId

  val tuple_row :
    nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val assignment_rows_tuple :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val tuple_problem :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val permutation_row :
    nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val assignment_rows_permutation :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val permutation_problem :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val combinations_from : nat -> nat -> nat -> nat list list

  val combinations : nat -> nat -> nat list list

  val combination_cols_aux : nat -> nat list -> coq_CCol list

  val combination_row :
    coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val indexed : 'a1 list -> (nat, 'a1) prod list

  val combination_problem :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val sum_nat : nat list -> nat

  val nonincreasing_from : nat -> nat list -> bool

  val nonincreasing : nat list -> bool

  val is_partition_of : nat -> nat list -> bool

  val partitions_bounded : nat -> nat -> nat -> nat list list

  val partitions_of : nat -> nat list list

  val partition_cols_aux : nat -> nat list -> coq_CCol list

  val partition_row :
    coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val partition_problem :
    nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val has_k_parts : nat -> nat list -> bool

  val is_partition_of_k : nat -> nat -> nat list -> bool

  val partitions_of_k : nat -> nat -> nat list list

  val partition_problem_k :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val subsets : nat list -> nat list list

  val nonempty_subsets : nat list -> nat list list

  val set_partition_row :
    coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val generated_set : nat -> nat list

  val set_partition_problem_values :
    nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val set_partition_problem_generated :
    nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val set_partition_k_row :
    nat -> nat -> nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId)
    Core.row

  val set_partition_k_rows_values :
    nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val set_partition_k_problem_values :
    nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val set_partition_k_problem_generated :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val multiset_partition_row :
    coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val generated_multiset : nat -> nat -> nat list

  val multiset_partition_problem :
    nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val multiset_partition_problem_generated :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val multiset_partition_k_row :
    nat -> nat -> nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId)
    Core.row

  val multiset_partition_k_rows :
    nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val multiset_partition_k_problem :
    nat -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val multiset_partition_k_problem_generated :
    nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val diag1 : nat -> nat -> nat

  val diag2 : nat -> nat -> nat -> nat

  val queen_id : nat -> nat -> nat -> coq_CRowId

  val queen_row :
    nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val queen_rows : nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val qrows : nat -> coq_CCol list

  val qcols : nat -> coq_CCol list

  val nqueens_problem : nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val langford_slots : nat -> coq_CCol list

  val langford_values : nat -> coq_CCol list

  val langford_row_id : nat -> nat -> nat -> coq_CRowId

  val langford_second_pos : nat -> nat -> nat

  val langford_start_count : nat -> nat -> nat

  val langford_row :
    nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val langford_rows_for_value :
    nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val langford_rows : nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val langford_problem :
    nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem

  val colorings : nat -> nat -> nat list list

  val progression : nat -> nat -> nat -> nat list

  val progression_in_bounds : nat -> nat -> nat -> nat -> bool

  val arithmetic_progressions : nat -> nat -> nat list list

  val color_at : nat list -> nat -> nat option

  val same_color_at : nat list -> nat -> nat -> bool

  val monochromatic_progression : nat list -> nat list -> bool

  val has_monochromatic_progression : nat -> nat -> nat -> nat list -> bool

  val waerden_good_coloring : nat -> nat -> nat -> nat list -> bool

  val waerden_good_colorings : nat -> nat -> nat -> nat list list

  val coloring_cols_aux : nat -> nat list -> coq_CCol list

  val waerden_coloring_row :
    coq_CRowId -> nat list -> (coq_CCol, coq_CColor, coq_CRowId) Core.row

  val waerden_rows :
    nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.row list

  val waerden_problem :
    nat -> nat -> nat -> (coq_CCol, coq_CColor, coq_CRowId) Core.problem
 end

module PublicAPI :
 sig
  val solve_ids_combinatorics :
    nat -> (Combinatorics.coq_CCol, Combinatorics.coq_CColor,
    Combinatorics.coq_CRowId) Core.problem -> Combinatorics.coq_CRowId list
    list

  val solve_ids_sudoku :
    nat -> (SudokuProblem.coq_GCol, SudokuProblem.coq_SColor,
    SudokuProblem.coq_SRowId) Core.problem -> SudokuProblem.coq_SRowId list
    list

  val solve_ids_warehouse :
    nat -> (Guaranteed_K_Warehouse.coq_WItem,
    Guaranteed_K_Warehouse.coq_WColor, Guaranteed_K_Warehouse.coq_WRowId)
    Core.problem -> Guaranteed_K_Warehouse.coq_WRowId list list

  val api_nqueens_ids : nat -> nat -> nat list list

  val api_langford_ids : nat -> nat -> nat list list

  val api_waerden_ids : nat -> nat -> nat -> nat -> nat list list

  val api_tuple_ids : nat -> nat -> nat -> nat list list

  val api_permutation_ids : nat -> nat -> nat -> nat list list

  val api_combination_ids : nat -> nat -> nat -> nat list list

  val api_partition_ids : nat -> nat -> nat list list

  val api_partition_k_ids : nat -> nat -> nat -> nat list list

  val api_set_partition_generated_ids : nat -> nat -> nat list list

  val api_set_partition_k_generated_ids : nat -> nat -> nat -> nat list list

  val api_multiset_partition_generated_ids :
    nat -> nat -> nat -> nat list list

  val api_multiset_partition_k_generated_ids :
    nat -> nat -> nat -> nat -> nat list list

  val api_sudoku_exact_ids : nat -> nat -> nat -> nat -> nat -> nat list list

  val api_sudoku_at_most_ids :
    nat -> nat -> nat -> nat -> nat -> nat list list

  val api_warehouse_guaranteed_ids : nat -> nat -> nat -> nat -> nat list list

  val api_warehouse_guaranteed_colored_ids :
    nat -> nat -> nat -> nat -> nat -> nat -> nat list list
 end
