open GT      
  
open Language
       
open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let check_jump x h = match x with
    | "z"  -> Value.to_int h = 0
    | "nz" -> Value.to_int h <> 0

let rec reduce_args f args stack = match args, stack with
  | [], t          -> List.rev f, stack
  | a::a', b::b' -> reduce_args ((a, b)::f) a' b'
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' -> 
    (match insn with
      | BINOP op -> let y :: x :: stack' = stack in eval env (cstack, (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y))) :: stack', c) prg'
      | CONST x  -> eval env (cstack, (Value.of_int x) :: stack, c) prg'
      | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) prg'
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) prg'
      | ST x     -> let r :: stack' = stack in eval env (cstack, stack', (State.update x r st, i, o)) prg'
      | STA (x, n) -> let t :: ind, stack' = split (n + 1) stack in eval env (cstack, stack', (Language.Stmt.update st x t (List.rev ind), i, o)) prg'
      | LABEL s  -> eval env conf prg'
      | JMP name -> eval env conf (env#labeled name)
      | CJMP (br, name) -> eval env (cstack, tl stack, c) ( if (check_jump br (hd stack)) then (env#labeled name) else prg')
      | CALL (f, n, p) -> if env#is_label f then eval env ((prg', st)::cstack, stack, c) (env#labeled f) else eval env (env#builtin conf f n p) prg'
      | BEGIN (_, args, locals) -> let res, newStack = reduce_args [] args stack in eval env (cstack, newStack, 
                                                 (List.fold_left (fun s (x, v) -> State.update x v s) (State.enter st (args @ locals)) res, i, o)) prg'
      | END | RET _ -> (match cstack with
                          | (prg', st') :: cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) prg'
                          | [] -> conf)
    )

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

class lG = object (self)
  val mutable label = 0
  method new_label = "label_" ^ string_of_int label, {<label = label + 1>}
end

let getName name = "L" ^ name

let rec compile' lG =
  let rec compile_e = function
  | Expr.Var   x -> [LD x]
  | Expr.Const n -> [CONST n]
  | Expr.Binop (op, x, y) -> compile_e x @ compile_e y @ [BINOP op]
  | Expr.String s -> [STRING s]
  | Expr.Call (f, params) -> List.concat (List.map compile_e params) @ [CALL (f, List.length params, false)] 
  | Expr.Array arr -> List.flatten (List.map compile_e arr) @ [CALL ("$array", List.length arr, false)]
  | Expr.Elem (arr, i) -> compile_e arr @ compile_e i @ [CALL ("$elem", 2, false)]
  | Expr.Length t -> compile_e t @ [CALL ("$length", 1, false)]
  | Expr.Call (f, args) -> call f args false
    and call f args p = let listArgs = List.map compile_e (List.rev args) in let argsCompiled = List.concat listArgs in argsCompiled @ [CALL (getName f, List.length args, p)]
      in function
    | Stmt.Seq (s1, s2) -> let l1, res1 = compile' lG s1 in let l2, res2 = compile' l1 s2 in l2, res1 @ res2
    | Stmt.Assign (x, [], e) -> lG, compile_e e @ [ST x]
    | Stmt.Assign (x, is, e) -> lG, List.flatten (List.map compile_e (is @ [e])) @ [STA (x, List.length is)]
    | Stmt.Skip -> lG, []
    | Stmt.If (condition, actionIf, actionElse) -> let cond = compile_e condition  and elseJ, l1 = lG#new_label in let endIfJ, l2 = l1#new_label in
        let l3, ifComp = compile' l2 actionIf in let l4, compiledElse = compile' l3 actionElse in
        l4, cond @ [CJMP ("z", elseJ)] @ ifComp @ [JMP endIfJ] @ [LABEL elseJ] @ compiledElse @ [LABEL endIfJ]
    | Stmt.While (condition, actionLoop) -> let cond = compile_e condition in let labelBegin, l1 = lG#new_label in let labelEnd, l2 = l1#new_label in
        let l3, actionLoopC = compile' l2 actionLoop in l3, [LABEL labelBegin] @ cond @ [CJMP ("z", labelEnd)] @ actionLoopC @ [JMP labelBegin] @ [LABEL labelEnd] 
    | Stmt.Repeat (actionLoop, condition) -> let cond = compile_e condition in let labelBegin, l1 = lG#new_label in let l2, actionLoopC = compile' l1 actionLoop in
        l2, [LABEL labelBegin] @ actionLoopC @ cond @ [CJMP ("z", labelBegin)]
    | Stmt.Call (f, args) -> lG, call f args true
    | Stmt.Return res -> lG, (match res with None -> [] | Some v -> compile_e v) @ [RET (res <> None)]

let func_defs lG (name, (args, locals, body)) = let endLabel, l1 = lG#new_label in let l2, funcC = compile' l1 body in
    l2, [LABEL name; BEGIN (name, args, locals)] @ funcC @ [LABEL endLabel; END]

let all_func_defs lG defs = List.fold_left (fun (lG, allDefsCode) (name, others) -> let l1, singleCode = func_defs lG (getName name, others) in l1, singleCode::allDefsCode) (lG, []) defs

let compile (defs, p) = let endLabel, l = (new lG)#new_label in 
  let l1, prog = compile' l p in 
  let l2, defsAll = all_func_defs l1 defs in 
  (prog @ [LABEL endLabel]) @ [END] @ (List.concat defsAll)
