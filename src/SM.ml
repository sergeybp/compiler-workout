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
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

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
    | CALL (f,_,_) -> eval env ((prg', st)::cstack, stack, c) (env#labeled f)
    | BEGIN (_,args, locals) -> let rec resolve acc args stack = match args, stack with
      | [], _ -> List.rev acc, stack
      | a::args', s::stack' -> resolve ((a, s)::acc) args' stack' in 
        let resolved, stack' = resolve [] args stack in
        let state' = (List.fold_left (fun s (x, v) -> State.update x v s) (State.enter st (args @ locals)) resolved, i, o) in
        eval env (cstack, stack', state') prg'
    | END -> ( match cstack with
      | (prg', st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) prg'
      | [] -> conf )

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

class lG = object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {<counter = counter + 1>} end 

let tmp x = "l_" ^ x

let rec cL lG =
  let rec compile_e e =
    match e with
    | Language.Expr.Const n -> [CONST n]
    | Language.Expr.Var x -> [LD x]
    | Language.Expr.Binop (op, e1, e2) -> compile_e e1 @ compile_e e2 @ [BINOP op] in function
  | Stmt.Seq (s1, s2)  -> let labels1, res1 = cL lG s1 in let labels2, res2 = cL labels1 s2 in labels2, res1 @ res2
  | Stmt.Read x        -> lG, [READ; ST x]
  | Stmt.Write e       -> lG, compile_e e @ [WRITE]
  | Stmt.Assign (x, e) -> lG, compile_e e @ [ST x]
  | Stmt.Skip          -> lG, []
  | Stmt.If (cond, ifA, elseA) -> let cC = compile_e cond in let lgElse, labels1 = lG#new_label in
    let lgFi, labels2 = labels1#new_label in let lg3, compiledIf = cL labels2 ifA in let lg4, compiledElse = cL lg3 elseA 
    in lg4, cC @ [CJMP ("z", lgElse)] @ compiledIf @ [JMP lgFi] @ [LABEL lgElse] @ compiledElse @ [LABEL lgFi]
  | Stmt.While (cond, loopA) -> let cC = compile_e cond in let labelBegin, labels1 = lG#new_label in
    let labelEnd, labels2 = labels1#new_label in let lg3, cLoopA = cL labels2 loopA 
    in lg3, [LABEL labelBegin] @ cC @ [CJMP ("z", labelEnd)] @ cLoopA @ [JMP labelBegin] @ [LABEL labelEnd] 
  | Stmt.Repeat (loopA, cond) -> let cC = compile_e cond in let labelBegin, labels1 = lG#new_label in
    let labels2, cLoopA = cL labels1 loopA in labels2, [LABEL labelBegin] @ cLoopA @ cC @ [CJMP ("z", labelBegin)]
  | Stmt.Call (f, args) -> let args_prg = List.concat @@ List.map compile_e args in (lG, args_prg @ [CALL (f, List.length args, true)])

let cF lG (name, (args, locals, body)) = let endLabel, labels1 = lG#new_label in
  let labels2, compiledFunction = cL labels1 body in
  labels2, [LABEL name; BEGIN (name, args, locals)] @ compiledFunction @ [LABEL endLabel; END]

let cA lG defs = 
  List.fold_left (fun (lG, allDefsCode) (name, others) -> let labels1, singleCode = cF lG (tmp name, others) in labels1, singleCode::allDefsCode)
    (lG, []) defs

let compile (defs, p) = let endLabel, lG = (new lG)#new_label in
  let l1, cP = cL lG p in 
  let _, allF = cA l1 defs in
  (LABEL "main" :: cP @ [LABEL endLabel]) @ [END] @ (List.concat allF)
