open Format
open Store
open Cycle

(* slim expression *)
type expr = Index of int | Lambda of int * expr | App of expr * expr
(* Lambda(N,exp) ... N nested lambda abstraction *)
(* \lambda(\lambda(...(\lambda exp)...)) *)

type algorithm = Naive | Floyd | Brent | Gosper

(* Num operators *)
(* let (?/) = num_of_int *)
(* let (!/) = string_of_num *)
(* let (%/) = mod_num *)

(* Variables for command-line options *)
let limit = ref 65535
let expr_str = ref ""
let init_exp = ref (Lambda(1,Index 1))
let no_eta = ref false
let loop_detection = ref Naive
let show_argnum = ref false
let show_bintree = ref false
let bind_vars = ref false
type display = Quiet | Verbose | Every of int
let display = ref Verbose

let rec unwrap_lambda = function
    Lambda(_,e) -> unwrap_lambda e
  | e -> e

let arg_num exp =
  let rec loop n = function
      App(e1,e2) -> loop (n+1) e1
    | _ -> n in
  loop 0 exp

let rec fst_arg = function
    App(Index _,e) -> e
  | App(e,_) -> fst_arg e
  | _ -> invalid_arg "fst_arg"

let rec depth_app = function
    App(e1,e2) -> 1 + max (depth_app e1) (depth_app e2)
  | _ -> 0

let rec size_app = function
    App(e1,e2) -> 1 + size_app e1 + size_app e2
  | _ -> 0

let rec spine_app = function
    App(e1,e2) -> 1 + spine_app e1
  | _ -> 0

let rec left_leaf_app = function
    App(Index _,e) -> 1 + left_leaf_app e
  | App(e1,e2) -> left_leaf_app e1 + left_leaf_app e2
  | _ -> 0

let rec lopsided_size k = function
    App(e1,e2) -> k + lopsided_size k e1 + lopsided_size (k+1) e2
  | _ -> 0

let rec lopsided_depth k exp =
  let rec lop_max i m = function
    [] -> m 
  | d::ds ->
      let d = if i=k+1 then d+1 else d in
      lop_max (i+1) (max m d) ds in
  let rec all_depth l = function
      App(Index _,e) -> lopsided_depth k e, l
    | App(e,Index _) -> all_depth (2::l) e
    | App(e1,e2) -> all_depth (lopsided_depth k e2::l) e1
    | Index _ -> 1,[]
    | Lambda(_,_) -> invalid_arg "lopsided_depth" in
  let d,ds = all_depth [] exp in
  d+lop_max 1 2 ds

let show_binnode node_str (ss1,sp1) (ss2,sp2) =
  let rec loop ss1 ss2 acc = match ss1 with
    | [] -> begin match ss2 with
        | [] -> List.rev acc
        | s2::ss2 -> loop [] ss2 ((sp1^" "^s2)::acc) end
    | s1::ss1 -> begin match ss2 with
        | [] -> loop ss1 [] ((s1^" "^sp2):: acc)
        | s2::ss2 -> loop ss1 ss2 ((s1^" "^s2):: acc) end in
  let w2 = String.length sp2 in
  if sp1 = "" then
    (String.make (w2-2)' '^"-"^node_str)::ss2, sp2
  else
    (match ss1 with
       | [] ->
           (sp1^String.make(w2-1)' '^"-"^node_str)::ss2
       | s1::ss1 ->
           loop ss1 ss2 [s1^String.make w2 '-'^node_str]), (sp1^" "^sp2)
      
let rec show_bin node_str = function
  | Index _ -> [], ""
  | Lambda(_,e) -> show_bin node_str e
  | App(e1,Index _) ->
      show_binnode node_str (show_bin "." e1) ([" |"],"  ")
  | App(e1,e2) ->
      show_binnode node_str (show_bin "." e1) (show_bin "|" e2) 

let print_bin t =
  List.iter (printf"\t%s@.") (fst (show_bin "+" t))

(* exp1[m:=exp2] *)
let rec subst exp1 exp2 m = match exp1 with
  | Index n as e -> begin match compare n m with
      |  1 (* n > m *) -> Index (pred n)
      | -1 (* n < m *) -> e
      | _  (* n = m *) -> rename n 1 exp2 end
  | Lambda(n,e) -> Lambda(n,subst e exp2 (m+n))
  | App(e1,e2) -> App(subst e1 exp2 m, subst e2 exp2 m)
  
and rename m i = function
  | Index j as e -> if j < i then e else Index(pred(j+m))
  | Lambda(n,e) -> Lambda(n,rename m (i+n) e)
  | App(e1,e2) -> App(rename m i e1, rename m i e2)

let rec beta = function
  | Index _ as e -> e
  | Lambda(n,e) -> Lambda(n,beta e)
  | App(e1,e2) -> match beta e1 with
      | Lambda(n,e) ->
          if n > 1 then Lambda(pred n, beta (subst e e2 n)) else beta (subst e e2 n)
      | e -> App(e, beta e2)

let rec free n = function
  | Index m -> m <> n 
  | Lambda(n',e) -> free (n+n') e
  | App(e1,e2) -> free n e1 && free n e2

exception Not_free
let rec reduce_if_free n = function
  | Index m as e -> begin match compare n m with
      |  1 (* n > m *) -> e
      | -1 (* n < m *) -> Index (pred m)
      | _  (* n = m *) -> raise Not_free end
  | Lambda(m,e) -> Lambda(n,reduce_if_free (n+m) e)
  | App(e1,e2) -> App(reduce_if_free n e1, reduce_if_free n e2)

let rec eta = function
  | Index _ as e -> e
  | Lambda(n,e) ->
      if n > 0 then match eta e with
        | App(e1, Index 1) as app ->
            begin try eta(Lambda(pred n,reduce_if_free 1 e1))
            with Not_free -> Lambda(n, app) end
        | e -> Lambda(n,e)
      else eta e
  | App(e1,e2) -> App(eta e1, eta e2)

let canonical expr = 
  let rec loop i = function
    | Index _ as e -> if i > 0 then Lambda(i,e) else e
    | Lambda(n,e) -> loop (i+n) e
    | App(e1,e2) ->
        if i > 0 then Lambda(i,App(loop 0 e1, loop 0 e2))
        else App(loop 0 e1, loop 0 e2) in
  loop 0 expr

let normalize e =
  if !no_eta then canonical (beta e) else canonical (eta (beta e))

let normalize_app e1 e2 =
  let after_beta = match e1 with
      Lambda(n,e) ->
        if n > 1 then Lambda(pred n, beta (subst e e2 n)) else beta (subst e e2 n)
    | _ -> assert false in
  if !no_eta then canonical after_beta else canonical (eta after_beta)

(* let num_to_alphabet n = char_of_int (n + 97) *)
let num_to_alphabet n = "xyzwvutsrqponmlkjihgfedcba".[n]

let num_to_var n =
  if n < 26 then sprintf "%c" (num_to_alphabet (n mod 26))
  else sprintf "%c%d" (num_to_alphabet (n mod 26)) (n/26)

let bind_free_variables expr =
  if !bind_vars then 
    let rec level = function
      | Index n -> n
      | Lambda(n,e) -> level e - n
      | App(e1,e2) -> max (level e1) (level e2) in
    let n = level expr in
    if n > 0 then Lambda(n,expr) else expr
  else expr

let string_of_expr expr =
  let rec with_fresh i = function
    | Index n ->
        if i < n then invalid_arg (sprintf "free variables found(%d<%d)" i n)
        else num_to_var (i-n)
    | Lambda(n,e) -> lambda n i e
    | App(e1,App(e2,e3)) ->
        sprintf "%s (%s)" (with_fresh i e1) (with_fresh i (App(e2,e3)))
    | App(e1,e2) -> 
        sprintf "%s %s" (with_fresh i e1) (with_fresh i e2)
  and lambda n i e =
    if n > 0 then sprintf "\\%s[%s]" (num_to_var i) (lambda (pred n) (succ i) e)
    else with_fresh i e in
  with_fresh 0 expr

let many_app init e n =
  let rec loop tmp n = if n < 1 then tmp else loop (beta(App(tmp,e))) (pred n) in
  loop init n

let self_app e n = many_app e e (pred n) 


module Expr = struct
  type t = expr
  let equal = (=)
  let compare = compare
  let hash = Hashtbl.hash
end
module MapStore = MakeMapStore(Expr)
module HashtblStore = MakeHashtblStore(Expr)
  
let argnum_str exp =
  if !show_argnum then
    let l, body = match exp with Lambda(l,b) -> l,b | _ -> 0,exp in
    sprintf " (l=%2d, m=%2d, n=%2d, s=%2d)"
(*       l (arg_num (fst_arg body)) (arg_num body-1) (lopsided_depth 0 body) *)
      l (arg_num (fst_arg body)) (size_app body) (left_leaf_app body)
  else ""

let print_state i e = match !display with
  | Quiet -> ()
  | Verbose ->
    printf "%3d%s => %s@." i (argnum_str e) (string_of_expr e);
    if !show_bintree then print_bin e
  | Every cycle ->
      if i mod cycle = 0 then eprintf "\r%d... %!" i

let rho_check init e =
  let module N = (Naive (struct
                          type t = expr
                          let limit = !limit
                          let next x = normalize_app x e
                          let next_impure x = next x
                          let copy x = x
                          let equal = (=)
                          let display = print_state
                        end) (HashtblStore)) in
  N.find_cycle init

(* Using Floyd's cycle finding algorithm *)
let rho_check_floyd init e =
  let e = normalize e in
  let init = normalize init in
  let module R = (Floyd (struct
                           type t = expr
                           let limit = !limit
                           let next x = normalize_app x e
                           let next_impure x = next x
                           let copy x = x
                           let equal = (=)
                           let display = print_state
                         end)) in
  R.find_cycle init

let rho_check_brent init e =
  let e = normalize e in
  let init = normalize init in
  let module R = (Brent (struct
                           type t = expr
                           let limit = !limit
                           let next x = normalize_app x e
                           let next_impure x = next x
                           let copy x = x
                           let equal = (=)
                           let display = print_state
                         end)) in
  R.find_cycle init

let rho_check_gosper init e =
  let e = normalize e in
  let init = normalize init in
  let module R = (Gosper (struct
                           type t = expr
                           let limit = !limit
                           let next x = normalize_app x e
                           let next_impure x = next x
                           let copy x = x
                           let equal = (=)
                           let display = print_state
                         end)) in
  R.find_cycle init

let church n =
  let rec loop e n = if n < 1 then e else loop (App(Index 2,e)) (pred n) in
  Lambda(2,loop (Index 1) n)

open Genlex
let lexer = make_lexer [ "(";")";"[";"]";"<";">";"{";"}";"\\" ]

let lexer_test s = Stream.npeek 1024 (lexer (Stream.of_string s))

external compare_string : string -> string -> int = "%compare"
module IdxMap = Map.Make(struct type t = string let compare = compare_string end)
let inc_idx idx = IdxMap.map succ idx

(* combinators *)
module CombMap = Map.Make(struct type t = string let compare = compare_string end)
let comb_alist = [
  "S", Lambda(3,App(App(Index 3, Index 1), App(Index 2, Index 1)));
  "K", Lambda(2,Index 2);
  "I", Lambda(1,Index 1);
  "B", Lambda(3,App(Index 3,App(Index 2,Index 1)));
  "C", Lambda(3,App(App(Index 3, Index 1), Index 2));
  "D", Lambda(4,App(App(Index 4,Index 3),App(Index 2,Index 1)));
  "E", Lambda(5,App(App(Index 5,Index 4),App(App(Index 3,Index 2),Index 1)));
  "F", Lambda(3,App(App(Index 1, Index 2), Index 3));
  "G", Lambda(4,App(App(Index 4, Index 1),
                                       App(Index 3, Index 2)));
  "H", Lambda(3,App(App(App(Index 3, Index 2), Index 1), Index 2));
  "J", Lambda(4,App(App(Index 4,Index 3),App(App(Index 4,Index 2),Index 1)));
  "L", Lambda(2,App(Index 2,App(Index 1, Index 1)));
  "M", Lambda(1,App(Index 1, Index 1));
  "O", Lambda(2,App(Index 1,App(Index 2, Index 1)));
  "Q", Lambda(3,App(Index 2,App(Index 3,Index 1)));
  "Q1", Lambda(3,App(Index 3,App(Index 1,Index 2)));
  "Q3", Lambda(3,App(Index 1,App(Index 3,Index 2)));
  "R", Lambda(3,App(App(Index 2, Index 1), Index 3));
  "T", Lambda(2,App(Index 1,Index 2));
  "U", Lambda(2,App(Index 1,App(App(Index 2,Index 2),Index 1)));
  "V", Lambda(3,App(App(Index 1, Index 3), Index 2));
  "W", Lambda(2,App(App(Index 2, Index 1), Index 1));
  "W1", Lambda(2,App(App(Index 1, Index 2), Index 2));
]
let comb_map =
  List.fold_left (fun map (s,e) -> CombMap.add s e map) CombMap.empty comb_alist
  
let str_to_expr idx str =
  try Index(IdxMap.find str idx)
  with Not_found -> try CombMap.find str comb_map
  with Not_found -> invalid_arg (sprintf "Unbound value '%s'" str)

let app eop e = match eop with None -> e | Some f -> App(f,e)
let comp_op eop =
  match eop with None -> None | Some f -> Some(Lambda(2,App(f,App(Index 2,Index 1))))

let rec parse_de_bruijn idx_map acc = parser
  | [< 'Ident "o";
        e2 = parse_de_bruijn idx_map (comp_op acc) >] -> e2
  | [< 'Ident s;
       e = parse_de_bruijn idx_map (Some(app acc (str_to_expr idx_map s))) >] -> e
  | [< 'Kwd"["; e1 = parse_de_bruijn (inc_idx idx_map) None; 'Kwd"]";
       e2 = parse_de_bruijn idx_map (Some(app acc (Lambda(1,e1)))) >] -> e2
  | [< 'Kwd"\\";'Ident x;'Kwd"[";
       e1 = parse_de_bruijn (IdxMap.add x 1 (inc_idx idx_map)) None; 'Kwd"]";
       e2 = parse_de_bruijn idx_map (Some(app acc (Lambda(1,e1)))) >] -> e2
  | [< 'Kwd"("; e1 = parse_de_bruijn idx_map None; 'Kwd")";
       e2 = parse_de_bruijn idx_map (Some(app acc e1)) >] -> e2
  | [< 'Int n; e = parse_de_bruijn idx_map (Some(app acc (Index n))) >] -> e
  | [< 'Kwd"<";'Int n;'Kwd">";
       e = parse_de_bruijn idx_map (Some(app acc (church n))) >] -> e
  | [< >] -> match acc with None -> invalid_arg "Parsing failure" | Some e -> e

let parse s =
  bind_free_variables (canonical (parse_de_bruijn IdxMap.empty None
                                    (lexer (Stream.of_string s))))

let usage_msg =
  "Usage: "^Sys.argv.(0)^
    " [-n limit|-no-limit] [-q|-s|-e num|-b] [-l] [-i init] 'expr'\n"^
    "\texpr ::= x | \\x[expr] | expr expr | (expr) | <num> | expr o expr | combinator\n"^
    "\t<num> denotes the church's numeral.\n"^
    "\tSome combinators are available. See all of them by the option '-l'."

let rec add_spec keys spec doc speclist = match keys with
  | [] -> speclist
  | key::keys' -> add_spec keys' spec doc ((key,spec," "^doc)::speclist)
let rec add_speclist ks_spcl spcl = match ks_spcl with
  | [] -> Arg.align spcl
  | (keys,spec,doc)::rest -> add_speclist rest (add_spec keys spec doc spcl)
let make_speclist ks_spcl = add_speclist ks_spcl []

let speclist = make_speclist [
  ["-a";"-argnum"], Arg.Set show_argnum,
  "Show the number of arguments (m = #args of fst arg, n = #args except fst args)";
  ["-n"], Arg.String(fun i-> limit := int_of_string i),
  "Limit number of self applications (default = "^string_of_int !limit^")";
  ["-u";"-unbound"], Arg.Unit(fun() -> limit := max_int-1),
  "Keep on trying self applications unless the rho-property is found";
  ["-l";"-list"], Arg.Unit(fun() ->
                   CombMap.iter
                     (fun s e -> printf "%s = %s\n" s (string_of_expr e)) comb_map;
                   exit 0),
  "List available combinators";
  ["-i";"-init"], Arg.String(fun str -> init_exp := parse str),
  "Initial expression";

  ["-q";"-quiet"], Arg.Unit(fun() -> display := Quiet),
  "Quiet mode";
  ["-e";"-every"], Arg.String(fun i -> display := Every(int_of_string i)),
  "Display only status every n";
  ["-ne";"-no-eta"], Arg.Set no_eta,

  "Skip eta reduction step for normalization";
  ["-p";"-print-bin"], Arg.Set show_bintree,
  "Print binary tree (lambda is ignored)";
  ["-f";"-floyd-cycle"], Arg.Unit(fun () -> loop_detection := Floyd),
  "Use Floyd's cycle-finding algorithm";
  ["-b";"-brent-cycle"], Arg.Unit(fun () -> loop_detection := Brent),

  "Use Improved Brent's cycle-finding algorithm";
  ["-g";"-gosper-cycle"], Arg.Unit(fun () -> loop_detection := Gosper),
  "Use Gosper's cycle-finding algorithm";

  ["-B";"-bind-free-variables"], Arg.Set bind_vars,
  "Bind all free variables";
]
(* let usage () = Arg.usage (Arg.align speclist) usage_msg *)
let usage () = Arg.usage speclist usage_msg

let anon_fun str = expr_str := !expr_str^" "^str

let _ =
  Arg.parse speclist anon_fun usage_msg;
  if String.length !expr_str = 0 then usage () else
    let e = parse !expr_str in
    let init = normalize_app !init_exp e in
    let show_mode mode_str =
      printf "Cycle detection mode: %s@." mode_str in
    let stime = Unix.gettimeofday() in
    let entry, cyc, exp = match !loop_detection with
    | Naive ->
       show_mode "Naive";
       rho_check init e
    | Floyd ->
       show_mode "Floyd";
       rho_check_floyd init e
    | Brent ->
       show_mode "Brent";
       rho_check_brent init e
    | Gosper ->
       show_mode "Gosper";
       rho_check_gosper init e in
    printf "%3d%s => %s@." entry (argnum_str exp) (string_of_expr exp);
    printf "Found! (%d = %d [%d])@." (entry+cyc) entry cyc;
    printf "Elapsed time: %.3f sec.@." (Unix.gettimeofday()-.stime)
