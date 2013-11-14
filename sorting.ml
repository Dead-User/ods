(* Sorting algorithms functional and imp *)

open Utils

module type SORT = 
  sig
    val selection_sort: 'a list -> 'a list
    val bubble_sort: 'a list -> 'a list
  end

(** Utils **)
let rec swap (l, n) =
    let rec loop xs count acc =
      match xs with
      | _ when count = n -> xs @ List.rev acc
      | [] -> List.rev acc
      | h::t -> loop t (count+1) (h::acc)
     in loop l 0 []

(* Mutable state for array swap *)
let array_swap xs i j =
  let temp = xs.(i) in
  xs.(i) <- xs.(j);
  xs.(j) <- temp
 
let rec bubble_sort l =
  let rec aux = function
    | [] -> []
    | x::y::xs -> 
       if x > y then y::aux(x::xs)
                else x::aux(y::xs)
    | x::xs -> x :: aux xs
  in let p = aux l in
  if l <> p then bubble_sort p
            else l

let selection_sort xs =
  let swap a i j =
    let temp = a.(i) in
    a.(i) <- a.(j); a.(j) <- temp
  and find_min arr i =
    let m = ref i in
    for j=i+1 to Array.length arr -1 do
      let mval = !m in
      if xs.(j) < xs.(mval) then m := j
    done;
    !m
  in
  let r = ref [] in
  for i = 0 to Array.length xs - 2 do
    let min = find_min xs i in
    swap xs i min
  done;
  xs

let rec selection_sort = function
    [] -> []
  | h::t ->
      let rec aux y ys = function
          [] -> y :: selection_sort ys
        | x::xs when x < y -> aux x (y::ys) xs
        | x::xs            -> aux y (x::ys) xs
      in
      aux h [] t

(* Tests *)

let unsorted = Utils.random_list 100 100
