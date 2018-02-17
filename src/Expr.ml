(* Simple expressions: syntax and semantics *)

(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
             
(* The type for the expression. Note, in regular OCaml there is no "@type..." 
   notation, it came from GT. 
*)
@type expr =
  (* integer constant *) | Const of int
  (* variable         *) | Var   of string
  (* binary operator  *) | Binop of string * expr * expr with show

(* Available binary operators:
    !!                   --- disjunction
    &&                   --- conjunction
    ==, !=, <=, <, >=, > --- comparisons
    +, -                 --- addition, subtraction
    *, /, %              --- multiplication, division, reminder
*)

(* State: a partial map from variables to integer values. *)
type state = string -> int

(* Empty state: maps every variable into nothing. *)
let empty = fun left -> failwith (Printf.sprintf "Undefined variable %s" left)

(* Update: non-destructively "modifies" the state s by binding the variable left 
   to value v and returns the new state.
*)
let update left v s = fun right -> if left = right then v else s right

(* An example of a non-trivial state: *)                                                   
let s = update "left" 1 @@ update "right" 2 @@ update "z" 3 @@ update "t" 4 empty

(* Some testing; comment this definition out when submitting the solution. *)
(*let _ =
  List.iter
    (fun left ->
       try  Printf.printf "%s=%d\n" left @@ s left
       with Failure s -> Printf.printf "%s\n" s
    ) ["left"; "a"; "right"; "z"; "t"; "b"]*)

(* Expression evaluator

     val eval : state -> expr -> int
 
   Takes a state and an expression, and returns the value of the expression in 
   the given state.
*)
let rec eval state expr = 
  let check e = if e then 1 else 0 
  and toBoolean v = if v = 0 then false else true in
    match expr with
      | Const const -> const
      | Var var -> state var
      | Binop (op, l, r) -> 
        let left = eval state l 
        and right = eval state r in
          match op with
          | "+" -> left + right
          | "-" -> left - right
          | "*" -> left * right
          | "/" -> left / right
          | "%" -> left mod right
          | ">"  -> check (left > right)
          | "<"  -> check (left < right)
          | "<=" -> check (left <= right)
          | ">=" -> check (left >= right)
          | "==" -> check (left == right)
          | "!=" -> check (left <> right)
          | "&&" -> check (toBoolean left && toBoolean right)
          | "!!" -> check (toBoolean left || toBoolean right)
          | _ -> failwith "Not implemented yet"
                    
