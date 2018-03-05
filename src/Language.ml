(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

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
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec getBinop = 
      let check e = if e then 1 else 0 
      and toBoolean v = if v = 0 then false else true in
        let bop = fun b left right -> check (b (toBoolean left) (toBoolean right)) and
        cop = fun c left right -> check (c left right) in function
          | "+" -> (+)
          | "-" -> (-)
          | "*" -> ( * )
          | "/" -> (/)
          | "%" -> (mod)
          | ">"  -> cop (>)
          | "<"  -> cop (<)
          | "<=" -> cop (<=)
          | ">=" -> cop (>=)
          | "==" -> cop (==)
          | "!=" -> cop (<>)
          | "&&" -> bop (&&)
          | "!!" -> bop (||)
          | _ -> failwith "Not implemented yet"

    let rec eval s = function
      | Const c          -> c
      | Var   v       -> s v
      | Binop (op, x, y) -> (getBinop op) (eval s x) (eval s y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
    )

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, i, o) = function
      | Read x -> Expr.update x (List.hd i) s, (List.tl i), o
      | Write y -> s, i, o@[Expr.eval s y]
      | Assign (x, y) -> Expr.update x (Expr.eval s y) s, i, o
      | Seq (y, y') -> eval (eval (s, i, o) y) y'
                                                         

    (* Statement parser *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
    )
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

  eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     

