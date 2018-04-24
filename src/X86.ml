(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
                                                                            
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
          
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)

let init n f =
  let rec init' i n f =
    if i >= n then []
    else (f i) :: (init' (i + 1) n f)
  in init' 0 n f

let make_pl_sub_mul op x y ret =
  [
  Mov (x, eax);
  Binop(op, y, eax); Mov (eax, ret); 
  ]

let make_div_mode op x y ret = 
  let move_cmd = match op with
    | "%" -> Mov (edx, ret)
    | "/" -> Mov (eax, ret)
    | _ -> failwith "Unsuported division op"
  in [
    Mov (L 0, edx); Mov (x, eax); Cltd; IDiv y; move_cmd;
  ]

let make_cmp op x y ret = 
  let suffix = match op with
    | "<"  -> "l"
    | "<=" -> "le"
    | ">"  -> "g"
    | ">=" -> "ge"
    | "==" -> "e"
    | "!=" -> "ne" 
    | _ -> failwith "Unexpected cmp op" 
    in
  [
    Mov (x, edx); Mov(y, eax);
    Binop("cmp", eax, edx); 
    Mov (L 0, eax); 
    Set(suffix, "%al");
    Mov(eax, ret);
  ]

let make_logic op x y ret = 
  [
  Binop ("^", eax, eax); Binop ("^", edx, edx);
  Binop ("cmp", L 0, x); Set ("nz", "%al");
  Binop ("cmp", L 0, y); Set ("nz", "%dl");
  Binop (op, eax, edx); Mov (edx, ret);
  ]

let rec pusha env z = function
  | 0 ->  env, z
  | n ->  let x, new_env = env#pop in
pusha new_env ((Push x)::z) (n-1)

let rec compile env code = match code with
  | [] -> env, []
  | instr :: code' ->
    let env, asm = match instr with
        | CONST value -> let s, env_new = env#allocate in env_new, [Mov (L value, s)]
        | WRITE -> let s, env_new = env#pop in env_new, [Push s; Call "Lwrite"; Pop eax]
        | LD name -> let s, env_new = (env#global name)#allocate in
          let loc_name = env_new#loc name in let cmds = 
            match s with 
              | S _ | M _ -> [Mov (loc_name, eax); Mov (eax, s)]
              | _ ->  [Mov (loc_name, s)]
          in env_new, cmds
        | ST name ->
          let s, env_new = (env#global name)#pop in
          let loc_name = env_new#loc name in 
          let cmds =  match s with 
              | S _ | M _ -> [Mov (s, eax); Mov (eax, loc_name)]
              | _ ->  [Mov (s, loc_name)]
          in env_new, cmds
        | READ -> let s, env_new = env#allocate in env_new, [Call "Lread"; Mov (eax, s)]
        | BINOP op ->
          let y, x, new_env = env#pop2 in
          let ret_val, new_env_2 = new_env#allocate in
          let asm_list_maker = match op with
            | "+" | "-" | "*" -> make_pl_sub_mul
            | "/" | "%" -> make_div_mode
            | "<" | "<=" | ">" | ">=" | "==" | "!=" -> make_cmp
            | "&&" | "!!" -> make_logic
            | _ -> failwith "Not supported binop"
          in new_env_2, asm_list_maker op x y ret_val
        | LABEL name -> env, [Label name]
        | JMP name -> env, [Jmp name]
        | CJMP (cond, name) -> let x, new_env = env#pop in new_env, [Binop ("cmp", L 0, x); CJmp (cond, name)]
        | BEGIN (name, params, locals) -> let new_env = env#enter name params locals in new_env, [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ new_env#lsize), esp)]
        | END -> env, [Label env#epilogue; Mov (ebp, esp); Pop ebp; Ret; Meta (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size))]
        | RET is_proc -> if is_proc then let x, env_new = env#pop in env_new, [Mov (x, eax); Jmp env_new#epilogue]
            else env, [Jmp env#epilogue]
        | CALL (f, param_count, is_proc) -> let pushed = List.map (fun x -> Push x) env#live_registers in
            let poped = List.map (fun x -> Pop x) @@ List.rev env#live_registers in
            let env_pop_func = fun (env, list) _ -> let s, env = env#pop in env, s::list in
            let env, params = List.fold_left env_pop_func (env, []) (init param_count (fun _ -> ())) in
            let params_rev = List.rev params in
            let push_params = List.map (fun x -> Push x) params_rev in
            let env, get_result = if is_proc then env, [] else (let s, env = env#allocate in env, [Mov (eax, s)]) in
            env, pushed @ push_params @ [Call f; Binop ("+", L (param_count * word_size), esp)] @ poped @ get_result
    in let env, asm' = compile env code' in env, asm @ asm'
                                
(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (init (List.length l) (fun x -> x))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+1
	| (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
	| _                             -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
      
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
