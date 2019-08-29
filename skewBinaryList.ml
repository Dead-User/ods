
(* Skew binary tree from Chris Okasaki's book purely functional data structure.
 * Featuring:
 *   (1). Constant time cons/tail/head operations (like list)
 *   (2). O(log(n)) time nth/set_nth operations *)

(* The idea is to used numbers to represent list-like data structures.
 * For example, cons is incr and tail is decr, and the size of a list
 * correspond to the value of a number *)
(* To support O(1) incr/decr, we use skew binary numbers.
 * In a binary number, every i-th bit has weight 2^(i-1).
 * In a skew binary number, every i-th bit has weight 2^i - 1.
 * Every bit in a skew binary number can be either 0, 1 or 2.
 * However, to restore uniqueness of number representation,
 * 2-bits are allowed only at the smallest non-zero bit.
 * This can be captured by the regular expression {0, 1}*2?0* *)
(* To get constant time incr/decr, we must have a way to skip leading zeros
 * at the lower end. To achieve so, we represent a number as a list
 * (weight * digit), where [weight] is the weight of the bit and [digit] is
 * 1 or 2. In this way, zeros never appear in the representation *)


(* To represent a 1-bit of weight w, we use a tree of size w.
 * Since all w has the form 2^i - 1, we use normal binary trees.
 * Since zero never appear is our representation and the tree is
 * always full, we use leaves rather that empty trees to save space *)
(* Note that to suport efficient head/tail, the order of elements is
 * root -> left sub-tree -> right sub-tree *)

type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a * 'a tree

(* Merge two given trees (of equal size), use an extra
 * value as the new tree's root. Related to incr/cons *)
let merge_tree v t1 t2 = Node(t1, v, t2)

(* Remove the root of a given tree, return its left and
 * right sub-tree (if any). Related to decr/tail *)
let remove_root = function
  | Leaf a -> None
  | Node(l, _, r) -> Some(l, r)

(* Get the root of a tree. Related to head *)
let get_root = function
  | Leaf r
  | Node(_, r, _) -> r

(* Get the [n]th element of a tree [t] of weight [w].
 * Related to nth *)
let rec nth_tree n (w, t) = 
  match t with
  (* Leaf nodes, we must have n = 0 *)
  | Leaf a when n = 0 -> a
  | Node(l, a, r) ->
      (* Since the root element is the first element,
       * return it if the index is zero *)
      if n = 0 then a else
      (* [w'] is the weight of sub-trees *)
      let w' = (w - 1) / 2 in
      (* Notice that [n] is 0-based and [w'] is 1-based.
       * After adjusting them to both 1- based,
       * we have [n] + 1 <= [w'] + 1, the left (+ 1) is
       * used to adjust their basis, and the right (+ 1)
       * means we have already skipped the root element. *)
      if n <= w' then
        nth_tree (n - 1) (w', l)
      else
        (* In this case, the index we are looking for is in
         * the right sub-tree. The relative offset of [n] in
         * [r] should be [n] - ([w'] + 1 [root]) *)
        nth_tree (n - w' - 1) (w', r)
  | _ -> failwith "SkewBinaryList.nth_tree"

(* The type of skew binary list is just a weighted list of trees.
 * Every tree correspond to a 1-digit. For possible 2-digits, by
 * definition they can only occur on the left-most non-zero bit.
 * But since we don't represent zero explicitly, this means that
 * 2-digits (if any) must occur on left-most. Therefore we can
 * represent 2-digits as two 1-digits of the same weight on the
 * head of the list *)
type weight = int
type 'a t = (weight * 'a tree) list

(* Insert an element into a skew binary list, takes O(1) *)
let insert v = function
  (* The first digit is 2. In this case, we merge
   * the two trees with the newly inserted element.
   * By definition the next bit in [ts] is at most 1,
   * so we won't violate the definition and will get
   * a well formed skew binary list. *)
  (* After inserting, we should have the order
   *   v -> t1 -> t2
   * Checking the definition of merge_tree shows that
   * this indeed holds after insertion *)
  | (w1, t1)::(w2, t2)::ts when w1 = w2 ->
      (* Actually [w1] + [w2] + 1 (the new element [v]) *)
      let w = w1 * 2 + 1 in
      (w, merge_tree v t1 t2)::ts
  (* The first non-zero bit is not 2 (no 2-digits).
   * Simply add a 1-digit to the first bit. *)
  | ts ->
      (1, Leaf v)::ts

(* Remove the first element from a skew binary list, takes O(1) *)
let tail = function
  | [] -> failwith "SkewBinaryList.remove"
  | (w, t)::ts ->
      (* The first node of the skew binary list is just the root 
       * of its first tree, since all trees are non-empty *)
      match remove_root t with
      | None -> ts
      | Some(l, r) ->
          (* By the invariant of a skew binary list,
           * we know that the first tree in [ts] (if any)
           * must have weight [w''] >= [w], hence we have
           * [w] < [w''], so we won't get a 3-digit. *)
          let w' = (w - 1) / 2 in
          (* The original order is root -> l -> r,
           * the new order is l -> r, as desired *)
          (w', l)::(w', r)::ts

(* The head of a skew binary list is just the root of its first tree, taes O(1) *)
let head = function
  | [] -> failwith "SkewBinaryList.head"
  | (w, t)::ts ->
      get_root t

(* Returns the [n]-th element of a skew binary list (if any), takes O(log(n)) *)
(* The O(log(n)) complexity of nth actually has nothing to do with the special
 * skew binary number represantiation. It is due to the logarithm shape of a
 * skew binary list. *)
let rec nth n = function
  | [] -> failwith "SkewBinaryList.nth" 
  | (w, t)::ts ->
      (* Notice that [n] is 0=based and [w] is 1-based, hence (>=) *)
      if n >= w then
        nth (n - w) ts
      else nth_tree n (w, t)

(* The length of a skew binary list is just the sum of the weight of 
 * all its trees, takes O(log(n)) *)
let length t = List.fold_left (fun l (w, _) -> l + w) 0 t;;


(* Auxiliary and slow functions converting between skew binary list and normal list, *)
let rec tree_to_list = function
  | Leaf a -> [a]
  | Node(l, a, r) ->
      tree_to_list l @ (a :: tree_to_list r)

let rec to_list = function
  | [] -> []
  | (w, t)::ts ->
      tree_to_list t @ to_list ts


module Test = struct
  let rec build n acc =
    if n <= 0 then acc
    else
      build (n - 1) (insert n acc)
  
  let op_o1 sbl =
    let sd = Random.int 2 in
    match sd with
    | 0 -> 
        let v = Random.int 120 in
        insert v sbl
    | _ -> tail sbl
  
  let op_ologn size sbl =
    let index = Random.int size in
    let _ = nth index sbl in
    ()
  
  
  let rec test_o1 n acc =
    if n <= 0 then acc
    else
      test_o1 (n - 1) (op_o1 acc)
  ;;
  
  let test_ologn size sbl =
    let rec loop n =
      if n <= 0 then ()
      else begin
        op_ologn size sbl;
        loop (n - 1)
      end
    in loop
  ;;
  
  let profile f =
    let t0 = Sys.time () in
    let res = f () in
    let t1 = Sys.time () in
    Format.printf "%f seconds used.\n" (t1 -. t0);
    res
  ;;
  
  (* Test with data sets of size 10^from to 10^up_to.
   * You can compare the time cost of different operations
   * on different sizes of datas to see their complexity *)
  let test ~from ~up_to =
    for i = from to up_to do
      let size = 
        let rec calc acc n = 
          if n <= 0 then acc else calc (acc * 10) (n - 1)
        in calc 1 i
      in
      Format.printf "Buiding tree of size %i...\n" size;
      let sbl = profile (fun () -> build size []) in
      Format.printf "Applying %i random O(1) operations...\n" size;
      let sbl = profile (fun () -> test_o1 size sbl) in
      Format.printf "Applying %i random O(log(n)) operations...\n" size;
      ignore @@ profile (fun () -> test_ologn (length sbl - 1) sbl size)
    done
end;;
