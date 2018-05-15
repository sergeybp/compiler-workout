(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let init n f =
  let rec init' i n f =
    if i >= n then []
    else (f i) :: (init' (i + 1) n f)
  in init' 0 n f

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope vs *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined v: %s" x)

    (* Bind a v to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the v x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a v in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of i")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* v           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an i stream, an o stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
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
    
let rec eval env ((st, i, o, r) as conf) expr = 
      match expr with
        | Const n ->  (st, i, o, Some (Value.of_int n))
        | Var x ->  (st, i, o, Some (State.eval st x))
        | Binop (op, x, y) -> let (_, _, _, Some x) as conf_x = eval env conf x in let (st, i, o, Some y) = eval env conf_x y in
            (st, i, o, Some (Value.of_int @@ to_func op (Value.to_int x) (Value.to_int y)))
        | Call (name, args) -> let (st, i, o, evaled_args) = eval_list env conf args in env#definition env name evaled_args (st, i, o, None)
        | String s -> (st, i, o, Some (Value.of_string s))
        | Array xs -> let (st, i, o, evaled_list) = eval_list env conf xs in env#definition env ".array" evaled_list (st, i, o, None)
        | Sexp (tag, exprs) -> let (st, i, o, evaled_exprs) = eval_list env conf exprs in (st, i, o, Some (Value.Sexp (tag, evaled_exprs)))
        | Elem (e, idx) -> let (st, i, o, args) = eval_list env conf [e; idx] in env#definition env ".elem" args (st, i, o, None)
        | Length e -> let (st, i, o, Some v) = eval env conf e in env#definition env ".length" [v] (st, i, o, None)
        and eval_list env conf xs = let vs, (st, i, o, _) = 
            List.fold_left (fun (acc, conf) x -> let (_, _, _, Some v) as conf = eval env conf x in v::acc, conf) ([], conf) xs in (st, i, o, List.rev vs)
         
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
      
     primary: s:sec k:(-"[" i:parse -"]" {`Elem i} | "." %"length" {`Len})* {
        List.fold_left (fun p -> function `Elem i -> Elem (p, i) | `Len -> Length p) s k
     };     
      sec:
        n:DECIMAL {Const n}
      | s:STRING {String (String.sub s 1 (String.length s - 2))}
      | x:IDENT  s: ("(" args: !(Util.list0)[parse] ")" {Call (x, args)} | empty {Var x}) {s}
      | c:CHAR {Const (Char.code c)}
      | "[" elements:!(Util.list0)[parse] "]" {Array elements}
      | "`" t:IDENT args:(-"(" !(Util.list)[parse] -")")? {Sexp (t, match args with None -> [] | Some x -> x)} 
      | -"(" parse -")"
  )
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for perns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse: empty {failwith "Not implemented"}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let bind x v s = (match s with | None -> None | Some s -> Some (State.bind x v s))

    let rec patrn patt v st = match patt, v with
         | Pattern.Ident  x, v -> bind x v st
         | Pattern.Wildcard, _ -> st
         | Pattern.Sexp (t, ps), Value.Sexp (t', vs) when t = t' -> match_list ps vs st
         | _ -> None
         and match_list ps vs s = (match ps, vs with
            | [], [] -> s
            | p::ps, v::vs -> match_list ps vs (patrn p v s)
            | _ -> None)


    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

  let rec eval env ((st, i, o, r) as conf) k stmt = let seq x ex = match ex with
    | Skip -> x
    | y -> Seq (x, y) in match stmt with
      | Assign (x, t, expr)  -> let (st, i, o, t) = Expr.eval_list env conf t in let (st, i, o, Some v) = Expr.eval env (st, i, o, None) expr in eval env (update st x v t, i, o, None) Skip k
      | If (expr, thenIf, elseIf) -> let (_, _, _, Some x) as conf = Expr.eval env conf expr in if Value.to_int x <> 0 then (eval env conf k thenIf) else (eval env conf k elseIf)
      | While (expr, loopStmt) -> let (_, _, _, Some x) as conf = Expr.eval env conf expr in
        if (Value.to_int x = 0) then eval env conf Skip k else eval env conf (seq stmt k) loopStmt      
      | Repeat (lS, expr) ->  eval env conf (seq (While (Expr.Binop ("==", expr, Expr.Const 0), lS)) k) lS
      | Seq (s1, s2) -> eval env conf (seq s2 k) s1
      | Skip -> (match k with Skip -> conf | something -> eval env conf Skip k)
      | Call (f, args) -> eval env (Expr.eval env conf (Expr.Call (f, args))) k Skip
      | Return res -> (match res with
        | None -> (st, i, o, None)
        | Some r -> Expr.eval env conf r)
      | Leave -> eval env (State.drop st, i, o, r) Skip k
      | Case (e, bs) -> let (_, _, _, Some v) as conf' = Expr.eval env conf e in let rec ch ((st, i, o, _) as conf) = function
          | [] -> eval env conf Skip k
          | (p, body)::tl -> match patrn p v (Some State.undefined) with
             | None     -> ch conf tl
             | Some st' -> eval env (State.push st st' (Pattern.vars p), i, o, None) k (Seq (body, Leave)) in ch conf' bs

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
        %"skip" {Skip}
      | %"if" e:!(Expr.parse)
    %"then" the:parse 
          elif:(%"elif" !(Expr.parse) %"then" parse)*
    els:(%"else" parse)? 
        %"fi" {
          If (e, the, 
           List.fold_right 
       (fun (e, t) elif -> If (e, t, elif)) 
       elif
       (match els with None -> Skip | Some s -> s)
          )
        }
      | %"while" e:!(Expr.parse) %"do" s:parse %"od"{While (e, s)}
      | %"for" i:parse "," c:!(Expr.parse) "," s:parse %"do" b:parse %"od" {
    Seq (i, While (c, Seq (b, s)))
        }
      | %"repeat" s:parse %"until" e:!(Expr.parse)  {Repeat (s, e)}
      | %"return" e:!(Expr.parse)?                  {Return e}
      | %"case" e:!(Expr.parse) %"of" bs:!(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)] %"esac" {Case (e, bs)}
      | x:IDENT 
           s:(is:(-"[" !(Expr.parse) -"]")* ":=" e   :!(Expr.parse) {Assign (x, is, e)}    | 
              "("  args:!(Util.list0)[Expr.parse] ")" {Call   (x, args)}
             ) {s}
    )     
  end


(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local vs, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (     
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator
     eval : t -> int list -> int list
   Takes a program and its i stream, and returns the o stream
*)

let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))

