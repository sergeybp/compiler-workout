open GT      
  
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config
   Takes a configuration and a program, and returns a configuration as a result
 *)                         

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' -> 
    match insn with
    | BINOP op -> let y::x::stack' = stack in eval env (cstack, Expr.to_func op x y :: stack', c) prg'
    | READ -> let z::i' = i in eval env (cstack, z::stack, (st, i', o)) prg'
    | WRITE -> let z::stack' = stack in eval env (cstack, stack', (st, i, o @ [z])) prg'
    | CONST i -> eval env (cstack, i::stack, c) prg'
    | LD x -> eval env (cstack, State.eval st x :: stack, c) prg'
    | ST x -> let z::stack' = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
    | LABEL _ -> eval env conf prg'
    | JMP l -> eval env conf (env#labeled l)
    | CJMP (cond, name) -> let x::stack' = stack in eval env (cstack, stack', c) (if ( (if cond = "nz" then x <> 0 else x = 0)) then (env#labeled name) else prg')

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let compile p =
  let  lG = object
    val mutable i = 0
    method get = i <- i + 1; "l_" ^ string_of_int i end
  in let rec compile_e e =
    match e with
    | Language.Expr.Const n -> [CONST n]
    | Language.Expr.Var x -> [LD x]
    | Language.Expr.Binop (op, e1, e2) -> compile_e e1 @ compile_e e2 @ [BINOP op]
  in let rec compile' p =
    match p with
    | Language.Stmt.Read x -> [READ; ST x]
    | Language.Stmt.Write e -> compile_e e @ [WRITE]
    | Language.Stmt.Assign (x, e) -> compile_e e @ [ST x]
    | Language.Stmt.Seq (st1, st2) -> compile' st1 @ compile' st2
    | Language.Stmt.Skip -> []
    | Language.Stmt.If (e, t, f) -> let else_label =  lG#get in let fi_label =  lG#get in compile_e e @ [CJMP ("z", else_label)] @ compile' t @ [JMP fi_label] @ [LABEL else_label] @ compile' f @ [LABEL fi_label]
    | Language.Stmt.While (e, s) -> let cond_label =  lG#get in let loop_label =  lG#get in [JMP cond_label] @ [LABEL loop_label] @ compile' s @ [LABEL cond_label] @ compile_e e @ [CJMP ("nz", loop_label)]
    | Language.Stmt.Repeat (s, e) -> let loop_label =  lG#get in [LABEL loop_label] @ compile' s @ compile_e e @ [CJMP ("z", loop_label)]
    | _ -> failwith "Undefined Behavior"
  in
  compile' p
