(* TEST
*)

(* We make object with id i have size about 100 * 2 ** i which allows us to
 * (approximately) deduce the reachable node ids just from the their total size. *)
let deduce_reachable size =
  let reachable = ref []
  and cur = ref 0
  and binary = ref (size / 100) in
  while !binary > 0 do
    if !binary land 1 = 1 then
      reachable := !cur :: !reachable;
    cur := !cur + 1;
    binary := !binary / 2
  done;
  List.rev !reachable

let expect_equal_int a e =
  if a <> e then
    Printf.printf "actual = %d; expected = %d\n" a e

let expect_equal_list a e =
  let string_of_arr x = List.map string_of_int x |> String.concat "," in
  if List.(a <> e) then
    Printf.printf "actual = %s; expected = %s\n" (string_of_arr a) (string_of_arr e)

let expect_reachable roots expected_individual expected_shared =
  let actual_individual, actual_shared = Obj.uniquely_reachable_words ~max_retainer_set_size:2
    (List.map Obj.repr roots |> Array.of_list) in
  let actual_individual = Array.to_list actual_individual in
  List.combine (List.map deduce_reachable actual_individual) expected_individual
  |> List.iter (fun (a, e) -> expect_equal_list a e);
  expect_equal_list (deduce_reachable actual_shared) expected_shared

let expect_exception f =
  try
    f ();
    Printf.printf "no exception\n"
  with
    | _ -> ()

type node = { id: int; used_memory: int array; mutable children: node list }
let make id ch = { id; used_memory = Array.make (Int.shift_left 100 id) 0; children = ch }

(* Note that this all needs to be in a function to ensure our nodes actually get
   allocated on the heap and are not static values in the binary (whose size we
   would not count) *)
let[@inline never] f () =
  let n10 = make 10 [] in
  let n9 = make 9 [] in
  let n8 = make 8 [] in
  let n7 = make 7 [n8] in
  let n6 = make 6 [n7; n8] in
  n7.children <- n6 :: n7.children;
  let n5 = make 5 [n9] in
  let n4 = make 4 [n6] in
  let n3 = make 3 [] in
  let n2 = make 2 [n3; n4] in
  let n1 = make 1 [n5; n10] in
  let n0 = make 0 [n3; n5] in
  let n14 = make 14 [] in
  let n13 = make 13 [n14] in
  let n12 = make 12 [n14] in
  let n11 = make 11 [n12; n13] in
  (*  /-> 10
   * 1 --> 5 --> 9
   *   /
   * 0 --> 3       ->8<
   *   /          /    \
   * 2 --> 4 --> 6 <--> 7
   *
   *   /-> 12 >--\
   * 11 -> 13 >- 14
   *)
  expect_reachable [n0; n1; n2] [[0]; [1; 10]; [2; 4; 6; 7; 8]] [3; 5; 9]; (* Proper roots *)
  expect_reachable [n0; n2; n1] [[0]; [2; 4; 6; 7; 8]; [1; 10]] [3; 5; 9]; (* check permutation doesn't matter *)
  expect_reachable [n1; n0; n2] [[1; 10]; [0]; [2; 4; 6; 7; 8]] [3; 5; 9];
  expect_reachable [n1; n2; n0] [[1; 10]; [2; 4; 6; 7; 8]; [0]] [3; 5; 9];
  expect_reachable [n2; n0; n1] [[2; 4; 6; 7; 8]; [0]; [1; 10]] [3; 5; 9];
  expect_reachable [n2; n1; n0] [[2; 4; 6; 7; 8]; [1; 10]; [0]] [3; 5; 9];
  expect_reachable [n1; n2] [[1; 5; 9; 10]; [2; 3; 4; 6; 7; 8]] [];
  expect_reachable [n0; n2] [[0; 5; 9]; [2; 4; 6; 7; 8]] [3];
  expect_reachable [n0; n1] [[0; 3]; [1; 10]] [5; 9];

  expect_reachable [n6; n7] [[6]; [7]] [8]; (* Cycles between roots *)
  expect_reachable [n6; n7; n2] [[6]; [7]; [2; 3; 4]] [8];
  expect_reachable [n6; n7; n8] [[6]; [7]; [8]] [];

  expect_reachable [n5; n9] [[5]; [9]] []; (* Root is parent of another root *)
  expect_reachable [n5; n9; n3] [[5]; [9]; [3]] [];
  expect_reachable [n5; n9; n3; n0] [[5]; [9]; [3]; [0]] [];
  expect_reachable [n1; n10; n5] [[1]; [10]; [5; 9]] [];

  expect_reachable [n12; n13] [[12]; [13]] [14]; (* Multiple owners *)
  expect_reachable [n12; n13; n14] [[12]; [13]; [14]] [];
  expect_reachable [n11; n12] [[11; 13]; [12]] [14];
  expect_reachable [n12; n11] [[12]; [11; 13]] [14];
  expect_reachable [n11; n12; n13] [[11]; [12]; [13]] [14];
  expect_reachable [n11] [[11; 12; 13; 14]] [];

  expect_reachable [n8; n9; n10] [[8]; [9]; [10]] []; (* Leaves *)

  ()
;;

(* Make sure invalid arguments for max_retainer_set_size cause an exception *)
let g () =
  let data = [| Obj.repr () |] in
  expect_exception (fun () -> Obj.uniquely_reachable_words ~max_retainer_set_size:(-3) data);
  expect_exception (fun () -> Obj.uniquely_reachable_words ~max_retainer_set_size:0 data);
  expect_exception (fun () -> Obj.uniquely_reachable_words ~max_retainer_set_size:1 data);
  expect_exception (fun () -> Obj.uniquely_reachable_words ~max_retainer_set_size:254 data);
  ignore (Obj.uniquely_reachable_words ~max_retainer_set_size:2 data);
  ignore (Obj.uniquely_reachable_words ~max_retainer_set_size:253 data);
  ()
;;

let flip f x y = f y x
let rec dedup = function
  | [] -> []
  | [x] -> [x]
  | x1 :: x2 :: r ->if x1 = x2 then dedup (x1 :: r) else x1 :: dedup (x2 :: r)

let[@inline never] h ~children_len ~parent_len () =
  Random.init 123;
  (* 840 divides the numbers 1 through 8 *)
  let children = List.init children_len (fun _ -> Array.make 839 0) |> Array.of_list in
  for max_retainer_set_size = 2 to 9 do
    (flip List.iter) [1; 2; 3; 5; 10; 25]
    (fun retainer_set_fraction ->
      let child_count_per_parent = children_len * max_retainer_set_size / parent_len / retainer_set_fraction in
      let parents_by_child = Array.make children_len [] in
      let parents = Array.make parent_len [] in
      for i = 0 to parent_len - 1 do
        for _ = 1 to child_count_per_parent do
          let j = Random.int children_len in
          parents.(i) <- children.(j) :: parents.(i);
          parents_by_child.(j) <- i :: parents_by_child.(j)
        done
      done;
      let expected_individual, expected_shared =
        Array.make parent_len (child_count_per_parent + 1), ref 0 in
      for j = 0 to children_len - 1 do
        let cur_parents = dedup parents_by_child.(j) in
        let len = List.length cur_parents in
        if len = 0 then
          ()
        else if len < max_retainer_set_size then
          let contribution = 840 / len in
          List.iter (fun i -> expected_individual.(i) <- contribution + expected_individual.(i))
            cur_parents
       else
         expected_shared := 840 + !expected_shared
      done;
      let actual_individual, actual_shared = Array.map (fun p -> Obj.repr (Array.of_list p)) parents
        |> Obj.uniquely_reachable_words ~max_retainer_set_size in
      expect_equal_list (Array.to_list actual_individual)
        (Array.to_list expected_individual);
      expect_equal_int actual_shared (!expected_shared))
  done
;;

let () = f ()
let () = g ()
let () = h ~children_len:1000 ~parent_len:200 ()
