(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
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
    let rec eval (s, i'::i, o) = function
      | Read x -> Expr.update x i' s, i, o
      | Write y -> s, i'::i, o@[Expr.eval s y]
      | Assign (x, y) -> Expr.update x (Expr.eval s y) s, i'::i, o
      | Seq (y, y') -> eval (eval (s, i'::i, o) y) y'
                                                         
  end
