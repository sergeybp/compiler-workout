open GT      
open Syntax 
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let eval' c i = match c, i with
	| (s, c), CONST x -> (x::s, c)
	| (s, (s', x::i, o)), READ -> (x::s, (s', i, o))
	| (x::s, (s', i, o)), WRITE -> (s, (s', i , o@[x]))
	| (s, (s', i, o)), LD x -> ((s' x)::s, (s', i, o))
	| (y::s, (s', i, o)), ST x -> (s, (Expr.update x y s', i, o))
	| (y::x::s, c), BINOP op -> ((Expr.getBinop op x y)::s, c)
	| _ -> failwith "Not yet implemented"

let rec eval config prog = match config, prog with
	| c, [] -> c 
	| c, i::p -> eval (eval' c i) p

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile' = function
	| Expr.Const x -> [CONST x]
	| Expr.Var x -> [LD x]
	| Expr.Binop (op, x, y) -> compile' x @ compile' y @ [BINOP op]

let rec compile = function
	| Stmt.Read x -> [READ; ST x]
	| Stmt.Write y -> compile' y @ [WRITE]
	| Stmt.Assign (x, y) -> compile' y @ [ST x]
	| Stmt.Seq (y, y')   -> compile y @ compile y'
