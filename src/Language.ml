(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty = {g = (fun x -> failwith (Printf.sprintf "Undefined variable %s" x)); l = (fun x -> failwith @@ Printf.sprintf "Unbound local variable %s" x); scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =  let up f y = if x = y then v else f y in if List.mem x s.scope then { s with l = up s.l }else { s with g = up s.g }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = { g = st.g; l = (fun x -> failwith (Printf.sprintf "Undefined variable %s" x)); scope = xs }

    (* Drops a scope *)
    let leave st st' = { st with g = st'.g }

  end
    
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
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                      
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
    *) 
    ostap (                                      
      parse:
    !(Ostap.Util.expr 
             (fun x -> x)
       (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
                `Lefta, ["!!"];
                `Lefta, ["&&"];
                `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
                `Lefta, ["+" ; "-"];
                `Lefta, ["*" ; "/"; "%"];
              |] 
       )
       primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt = match stmt with
      | Read x -> (match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write e -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (State.update x (Expr.eval st e) st, i, o)
      | If (expr, thenIf, elseIf) -> if (Expr.eval st expr) <> 0 then (eval env conf thenIf) else (eval env conf elseIf)
      | While (expr, lS) -> rwL env conf expr lS
      | Seq (s1, s2) -> eval env (eval env conf s1) s2
      | Skip -> conf
      | Repeat (lS, expr) ->  rwL env (eval env conf lS) expr lS
      | Call (f, args) -> let computedArgs = List.map (Expr.eval st) args in
          let formals, locals, body = env#definition f in
          let methodState = State.enter st (formals@locals) in
          let argsMapping = List.combine formals computedArgs in
          let fullMethodState = List.fold_left (fun st (x, a) -> State.update x a st) methodState argsMapping in
          let resultState, resultInput, resultOutput = eval env (fullMethodState, i, o) body in
          (State.leave resultState st, resultInput, resultOutput) and rwL env ((st, _, _) as conf) expr lS = if (Expr.eval st expr) != 0 then rwL env (eval env conf lS) expr lS else conf

    let rec parsEI eIf el =  match eIf with
          | [] -> el
          | (condition, action)::tEI -> If (condition, action, parsEI tEI el)

    let parseEl eIf el = let elseActionParsed = match el with
      | None -> Skip
      | Some action -> action in parsEI eIf elseActionParsed
                                
    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        "read" "(" x:IDENT ")" {Read x}
      | "write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT 
        assignmentOrCall: (
          ":=" e:!(Expr.parse) {Assign (x, e)}
          | "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)}
        ) {assignmentOrCall}
      | %"skip"                         {Skip}
      | %"if" condition: !(Expr.parse) %"then" action:parse 
        eIf:(%"elif" !(Expr.parse) %"then" parse)*
        el:(%"else" parse)?
        %"fi" { If (condition, action, parseEl eIf el)}
      | %"while" condition: !(Expr.parse) %"do" action:parse %"od" { While (condition, action) }
      | %"repeat" action:parse %"until" condition: !(Expr.parse) { Repeat (action, condition) }
      | %"for" initialize:parse "," condition: !(Expr.parse)
        "," increment:parse %"do" action:parse %"od" {Seq (initialize, While (condition, Seq (action, increment)))}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      argument: IDENT;
      parse: %"fun" functionName:IDENT "(" args: !(Util.list0 argument) ")"
        locals: (%"local" !(Util.list argument))?
        "{" body: !(Stmt.parse) "}" { (functionName, (args, (match locals with None -> [] | Some l -> l), body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator
     eval : t -> int list -> int list
   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = let module CM = Map.Make (String) in
  let defsM = List.fold_left (fun m ((name, _) as defs) -> CM.add name defs m) CM.empty defs in
  let envObject = (object method definition name = snd (CM.find name defsM) end) in
  let _, _, output = Stmt.eval envObject (State.empty, i, []) body in output
                                   
(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))