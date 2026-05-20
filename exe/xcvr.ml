(* xcvr.ml

   Native GDance demo runner.

   This mirrors the examples exposed by the browser demo, but runs on native
   OCaml instead of inside the browser.

   The repository intentionally does not distribute prebuilt executables or
   shared libraries. Users who want native execution can build from source:

     dune build
     dune exec ./exe/xcvr.exe

   or, depending on your directory layout:

     dune exec ./native/xcvr.exe

   The output is the raw row-id solution form returned by the extracted
   solve_ids-style APIs.
*)

(* Note on decoded output:

   The native runner currently prints raw row-id solutions, matching the
   extracted solve_ids-style APIs.  The browser demo includes additional
   TypeScript-side decoding for user-facing display.

   A future version may add Rocq-side decoded APIs so that browser and native
   frontends can share mathematical decoders extracted from GDance.v.
*)

open Printf

module API = Gdance.PublicAPI

(* -------------------------------------------------------------------------- *)
(* Rocq nat/list conversion                                                   *)
(* -------------------------------------------------------------------------- *)

let rec nat_of_int n =
  if n <= 0 then Gdance.O
  else Gdance.S (nat_of_int (n - 1))

let rec int_of_nat = function
  | Gdance.O -> 0
  | Gdance.S n -> 1 + int_of_nat n

let rec list_to_ocaml = function
  | Gdance.Nil -> []
  | Gdance.Cons (x, xs) -> x :: list_to_ocaml xs

let n = nat_of_int

(* -------------------------------------------------------------------------- *)
(* Human-friendly wrappers around extracted APIs                              *)
(*                                                                            *)
(* The extracted Rocq APIs are positional and use Rocq nat/list types.         *)
(* These wrappers expose named OCaml arguments in the same order as the web    *)
(* demo URLs, then call the extracted API in its Rocq/extraction order.        *)
(*                                                                            *)
(* Current convention: extracted API wrappers take fuel first.                 *)
(* -------------------------------------------------------------------------- *)

let nqueens ~n:nn ~fuel =
  API.api_nqueens_ids (n fuel) (n nn)

let langford ~n:nn ~fuel =
  API.api_langford_ids (n fuel) (n nn)

let waerden ~n:nn ~q ~k ~fuel =
  API.api_waerden_ids (n fuel) (n nn) (n q) (n k)

let tuple ~n:nn ~k ~fuel =
  API.api_tuple_ids (n fuel) (n k) (n nn)

let permutation ~n:nn ~k ~fuel =
  API.api_permutation_ids (n fuel) (n k) (n nn)

let combination ~n:nn ~k ~fuel =
  API.api_combination_ids (n fuel) (n k) (n nn)

let partition ~n:nn ~fuel =
  API.api_partition_ids (n fuel) (n nn)

let partition_k ~n:nn ~k ~fuel =
  API.api_partition_k_ids (n fuel) (n nn) (n k)

let set_partition_generated ~n:nn ~fuel =
  API.api_set_partition_generated_ids (n fuel) (n nn)

let set_partition_k_generated ~n:nn ~k ~fuel =
  API.api_set_partition_k_generated_ids (n fuel) (n k) (n nn)

let multiset_partition_generated ~n:nn ~label_count ~fuel =
  API.api_multiset_partition_generated_ids
    (n fuel) (n nn) (n label_count)

let multiset_partition_k_generated ~n:nn ~k ~label_count ~fuel =
  API.api_multiset_partition_k_generated_ids
    (n fuel) (n k) (n nn) (n label_count)

    let sudoku_exact ~r_cap ~c_cap ~r ~c ~fuel =
  API.api_sudoku_exact_ids
    (n fuel) (n r_cap) (n c_cap) (n r) (n c)

let sudoku_at_most ~r_cap ~c_cap ~r ~c ~fuel =
  API.api_sudoku_at_most_ids
    (n fuel) (n r_cap) (n c_cap) (n r) (n c)

let warehouse_guaranteed ~n_items ~n_sources ~k ~fuel =
  API.api_warehouse_guaranteed_ids
    (n fuel) (n n_items) (n n_sources) (n k)

let warehouse_guaranteed_colored
    ~n_items ~n_sources ~n_product_colors ~n_source_reqs ~k ~fuel =
  API.api_warehouse_guaranteed_colored_ids
    (n fuel)
    (n n_items)
    (n n_sources)
    (n n_product_colors)
    (n n_source_reqs)
    (n k)

(* -------------------------------------------------------------------------- *)
(* Pretty printing                                                            *)
(* -------------------------------------------------------------------------- *)

let print_nat_list xs =
  let xs = list_to_ocaml xs in
  printf "[";
  List.iteri
    (fun i x ->
      if i > 0 then printf "; ";
      printf "%d" (int_of_nat x))
    xs;
  printf "]"

let print_nat_list_list xss =
  let xss = list_to_ocaml xss in
  printf "[\n";
  List.iter
    (fun xs ->
      printf "  ";
      print_nat_list xs;
      printf ";\n")
    xss;
  printf "]\n"

let print_result name result =
  let result_as_ocaml = list_to_ocaml result in
  printf "\n== %s ==\n" name;
  printf "solution count: %d\n" (List.length result_as_ocaml);
  print_nat_list_list result

let run name f =
  try print_result name (f ())
  with exn ->
    printf "\n== %s ==\n" name;
    printf "ERROR: %s\n" (Printexc.to_string exn)

(* -------------------------------------------------------------------------- *)
(* Demo catalog                                                               *)
(* -------------------------------------------------------------------------- *)

let () =
  printf "GDance native runner\n";
  printf "=========================\n";
  printf "These examples mirror the public browser API catalog.\n";
  printf "For large searches, native execution is preferred over browser execution.\n";
  printf "\n";
  printf "Output note:\n";
  printf "  This native runner currently prints raw row-id solutions.\n";
  printf "  A row id names a candidate row/choice in the exact-cover model;\n";
  printf "  it is not always the mathematical value being modeled.\n";
  printf "  The browser demo includes additional TypeScript-side decoding for\n";
  printf "  user-facing display. If there is sufficient interest, future versions\n";
  printf "  may add Rocq-side decoded APIs so browser and native frontends can\n";
  printf "  share the same mathematical decoders extracted from GDance.v.\n";
  printf "\n";

  (* ---------------------------------------------------------------------- *)
  (* Basic exact-cover / combinatorics examples                              *)
  (* ---------------------------------------------------------------------- *)

  run "nqueens n=4 fuel=10"
    (fun () -> nqueens ~n:4 ~fuel:10);

  run "langford n=3 fuel=10"
    (fun () -> langford ~n:3 ~fuel:10);

  run "langford n=4 fuel=20"
    (fun () -> langford ~n:4 ~fuel:20);

  run "waerden n=3 q=2 k=3 fuel=10"
    (fun () -> waerden ~n:3 ~q:2 ~k:3 ~fuel:10);

  run "tuple n=3 k=2 fuel=10"
    (fun () -> tuple ~n:3 ~k:2 ~fuel:10);

  run "permutation n=4 k=2 fuel=10"
    (fun () -> permutation ~n:4 ~k:2 ~fuel:10);

  run "combination n=5 k=3 fuel=10"
    (fun () -> combination ~n:5 ~k:3 ~fuel:10);

  (* ---------------------------------------------------------------------- *)
  (* Integer, set, and multiset partitions                                   *)
  (* ---------------------------------------------------------------------- *)

  run "partition n=5 fuel=20"
    (fun () -> partition ~n:5 ~fuel:20);

  run "partition_k n=5 k=2 fuel=20"
    (fun () -> partition_k ~n:5 ~k:2 ~fuel:20);

  run "set_partition_generated n=4 fuel=10"
    (fun () -> set_partition_generated ~n:4 ~fuel:10);

  run "set_partition_k_generated n=5 k=2 fuel=10"
    (fun () -> set_partition_k_generated ~n:5 ~k:2 ~fuel:10);

  run "multiset_partition_generated n=4 label_count=2 fuel=20"
    (fun () ->
      multiset_partition_generated
        ~n:4
        ~label_count:2
        ~fuel:20);

  run "multiset_partition_k_generated n=4 k=2 label_count=2 fuel=20"
    (fun () ->
      multiset_partition_k_generated
        ~n:4
        ~k:2
        ~label_count:2
        ~fuel:20);

  (* ---------------------------------------------------------------------- *)
  (* Sudoku-style examples                                                   *)
  (* ---------------------------------------------------------------------- *)

  run "sudoku_exact R=2 C=2 r=2 c=2 fuel=20"
    (fun () ->
      sudoku_exact
        ~r_cap:2
        ~c_cap:2
        ~r:2
        ~c:2
        ~fuel:20);

  run "sudoku_at_most R=1 C=2 r=2 c=2 fuel=20"
    (fun () ->
      sudoku_at_most
        ~r_cap:1
        ~c_cap:2
        ~r:2
        ~c:2
        ~fuel:20);

  (* ---------------------------------------------------------------------- *)
  (* Warehouse / scheduling-style generated examples                         *)
  (* ---------------------------------------------------------------------- *)

  run "warehouse_guaranteed n_items=12 n_sources=4 n_source_reqs=2 k=3 fuel=10"
    (fun () ->
      warehouse_guaranteed
        ~n_items:12
        ~n_sources:4
        ~k:3
        ~fuel:10);

  run
    "warehouse_guaranteed_colored n_items=12 n_sources=4 n_product_colors=3 n_source_reqs=2 k=3 fuel=10"
    (fun () ->
      warehouse_guaranteed_colored
        ~n_items:12
        ~n_sources:4
        ~n_product_colors:3
        ~n_source_reqs:2
        ~k:3
        ~fuel:10);

  printf "\nDone.\n"