(* Search *)

open Utils

module type SEARCHALG = sig
  val linear : 'a -> 'a list -> 'a option
  val binary : 'a -> 'a list -> 'a option
end

module Search : SEARCHALG = struct
  (* Nice easy one to start with *)
  let rec linear ~element:v = function
    | [] -> None
    | x::xs -> if x = v then Some(x) else linear v xs

  let binary ~element:v xs =
    let rec aux element xs min max =
      (* Base clause *)
      if min = max then
        None (* TODO *)
      else (* Inductive *)
        let t = min + max
        and mid = t / 2
        in Some(t)
    in match xs with
      | [] -> None
      | x::xs as lst -> 
          aux v lst 0 (List.length xs)
end