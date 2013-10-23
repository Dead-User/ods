(* Binary Trees *)

type 'a tree =
  | Leaf
  | Node of 'a tree * 'a * 'a tree

module type BTree = sig
  val insert : 'a -> 'a tree -> 'a tree
  val member : 'a -> 'a tree -> bool
  val size   : 'a tree -> int
end

let rec insert v = function
  | Leaf -> Node(Leaf, v, Leaf)
  | Node(l,item,r)
     (* Insertion on the left subtree *)
      -> if v < item then Node((insert v l), item, r)
     (* Insertion on the right subtree *)
         else if v > item then Node(l, item, (insert v r))
         else Node(l, item, r)

let rec member x = function
  | Leaf -> false
  | Node(l,v,r) ->
      if x=v then true
      else if x < v then member x l
      else member x r

let rec height = function
  | Leaf -> 0
  | Node(l,_,r) -> 1 + (max (height l) (height r))

(* Build a tree from a list *)
let make_tree = 
  List.fold_left 
    (fun acc v -> insert v acc) Leaf

(* Traversals *)
(* *************************************************** *)

let rec preorder = function
    Leaf -> []
  | Node(l,v,r) -> v::((preorder l) @ (preorder r))

let rec inorder = function
    Leaf -> []
  | Node(l,v,r) -> (inorder l) @ v::(inorder r)
