open Format
open Store
open Cycle
open Bexpr

let limit = ref 65535
type howshow =
  Sum | Length | Height | Depth | Value of string | BarChart
type algo = Naive | Floyd | Brent | Gosper | Gosper2
type store = Map | Hashtbl
type display = Quiet | Verbose | Every of int | Show of howshow list

let restart_file : string option ref = ref None
let algo = ref Naive
let store = ref Hashtbl
let bexpr = ref (module LevelList: Expr)
let display = ref Verbose
let blist = ref []
let wid = ref 1

let show_algo algo_str =
  printf "Cycle detection algorithm: %s@." algo_str

let abort_unless_int63 () =
  if (-1) lsr 1 + 1 <> 1 lsl 62 then
    failwith"This mode assumes 63-bit int."

let internal_expr_alist = [
    ("LL", fun () -> bexpr := (module LevelList));
    ("BL", fun () -> bexpr := (module NonReuseBytes));
    ("RB", fun () -> bexpr := (module ReuseBytes));
    ("RE", fun () -> bexpr := (module ReuseBytesExtensible));
    ("ZB", fun () -> bexpr := (module ZBytes));
    ("RL", fun () -> bexpr := (module RevList));
    ("ZS", fun () -> bexpr := (module MakeBitSeq(ZBits)));
    ("LS", fun () -> abort_unless_int63 ();
                     bexpr := (module MakeBitSeq(LBits)));
    ("IS", fun () -> (* NOT RECOMMENDED *)
                     bexpr := (module MakeBitSeq(IntBits)));
    ("DS", fun () -> (* NOT RECOMMENDED *)
                     abort_unless_int63 ();
                     bexpr := (module MakeBitSeq(DIntBits)));
    ("TS", fun () -> (* NOT RECOMMENDED *)
                     abort_unless_int63 ();
                     bexpr := (module MakeBitSeq(TIntBits)));
]

(* Generating Expr-dependent functions for main *)
module MakeMain(B:Expr) = struct

  let pp_expr wid prf expr =
    match B.list_of_expr expr with
    | [] -> invalid_arg "BitSeq.pp_expr"
    | hd::tl ->
       fprintf prf "%*d" wid hd; List.iter (fprintf prf ".%*d" wid) tl

  (* fold expr lower to higher *)
  (* f 5 (f 2 (f 2 (f 1 (f 1 (f 0 e)))))  for 5.2.2.1.1.0 *)
  let expr_fold_up f e exp =
    List.fold_left (fun x i -> f i x) e (B.rev_list_of_expr exp)
    
  (* fold expr lower to higher *)
  (* f 0 (f 1 (f 1 (f 2 (f 2 (f 5 e)))))  for 5.2.2.1.1.0 *)
  let expr_fold_down f e exp =
    List.fold_left (fun x i -> f i x) e (B.list_of_expr exp)

  let expr_sum expr = expr_fold_up (+) 0 expr
  let expr_length expr = expr_fold_up (fun _->succ) 0 expr
  let expr_height expr =
    1 + expr_fold_up max 0 expr (* Bytes.length expr *)
  let expr_depth expr =
    fst (expr_fold_down (fun h (d,i) -> (max (i+h) d, i+1)) (0,0) expr)

  let expr_value str expr =
    Arithexp.parse
      (function
         | "S" -> expr_sum expr
         | "L" -> expr_length expr
         | "H" -> expr_height expr
         | "D" -> expr_depth expr
         | s -> failwith (s^": unknown variable")) str
    
  let expr_countzeros expr =
    expr_fold_up (fun h c->if h=0 then succ c else c) 0 expr
    
  let pp_bar_chart prf expr =
    fprintf prf "@[";
    ignore (expr_fold_down (fun h b ->
                if b then fprintf prf "@\n";
                for i = 1 to h do fprintf prf "#" done;
                true) false expr);
    fprintf prf "@]"
    
  let pp_howshow expr prf = function
    | Sum -> fprintf prf "S=%3d" (expr_sum expr)
    | Length -> fprintf prf "L=%3d" (expr_length expr)
    | Height -> fprintf prf "H=%3d" (expr_height expr)
    | Depth -> fprintf prf "D=%3d" (expr_depth expr)
    | Value s -> fprintf prf "%s=%3d" s (expr_value s expr)
    | BarChart -> pp_bar_chart prf expr
                
  let pp_howshow_list expr prf = function
    | [] -> invalid_arg "pp_howshow_list"
    | hs::rest ->
       fprintf prf "@[%a" (pp_howshow expr) hs;
       List.iter (fprintf prf ",@;%a" (pp_howshow expr)) rest;
       fprintf prf "@]"
       
  let show_status disp = match disp with
    | Quiet -> (fun i exp -> ())
    | Every cycle ->
       (fun i exp -> if i mod cycle = 0 then eprintf "\r%d... %!" i)
    | Verbose ->
       (fun i exp -> printf "%3d => %a@." i (pp_expr !wid) exp)
    | Show hss ->
       (fun i exp -> 
         printf "%d => [%a] %a@." i 
           (pp_howshow_list exp) (List.rev hss) (pp_expr !wid) exp)

  let make_stmod: store -> (module StoreType with type t = B.t) =
    function
    | Map -> (module MakeMapStore(B))
    | Hashtbl -> (module MakeHashtblStore(B))

  let make_exprtype expr: (module ExprType with type t = B.t) =
    let init = B.copy expr in
    let next_impure =
      if expr_length expr = 1 then
        let h = expr_height expr-1 in
        (fun e -> B.apply_mono e h) 
      else
        (fun e -> B.apply e init) in
    (module (struct
              type t = B.t
              let limit = !limit
              let next_impure = next_impure
              let next e = next_impure (B.copy e)
              let copy x = B.copy x
              let hash = B.hash
              let equal = B.equal
              let display = show_status !display
            end))

  let rho_check expr = match !algo with
    | Naive ->
       show_algo "Naive";
       let module M =
         Naive(val make_exprtype expr)(val make_stmod !store) in
       M.find_cycle expr
    | Floyd -> begin
        match !restart_file with
        | None ->
           show_algo "Floyd";
           let module M = Floyd(val make_exprtype expr) in
           M.find_cycle expr
        | Some fname ->
           show_algo "Restartable (Floyd)";
           let module M = RestartableFloyd(val make_exprtype expr) in
           M.find_cycle_restart expr fname
      end
    | Brent -> begin
        match !restart_file with
        | None ->
           show_algo "Brent";
           let module M = ImprovedBrent(val make_exprtype expr) in
           M.find_cycle expr
        | Some fname ->
           show_algo "Restartable (Brent)";
           let module M = RestartableBrent(val make_exprtype expr) in
           M.find_cycle_restart expr fname
      end
    | Gosper -> begin
        match !restart_file with
        | None ->
           show_algo "Gosper";
           let module M = Gosper(val make_exprtype expr) in
           M.find_cycle expr
        | Some fname ->
           eprintf "Restartable (Gosper): not implemented yet@.";
           exit 1
      end
    | Gosper2 ->
       match !restart_file with
       | None ->
          show_algo "Gosper2";
          let module M = ImprovedGosper(val make_exprtype expr) in
          M.find_cycle expr
       | Some fname ->
          eprintf "Restartable (Gosper): not implemented yet@.";
          exit 1

  let main () =
    (* Arg.parse speclist anon_fun usage_msg; *)
    let expr = B.expr_of_list (List.rev !blist) in
    if !display = Quiet then
      printf "%3d => %a@." 1 (pp_expr !wid) expr;
    let stime = Unix.gettimeofday() in
    let start, cycle, exp = rho_check expr in
    let ftime = Unix.gettimeofday() in
    printf "Found! (%d = %d [%d])@." (start+cycle) start cycle;
    printf "%d => %a@." start  (pp_expr !wid) exp;
    if !restart_file = None then
      printf "Elapsed time: %.3f sec.@." (ftime-.stime)

end

let run_monomial_test () =
  display := Quiet;
  limit := Pervasives.max_int-1;
  (* Known results in monomial cases *)
  let tests = [|(6,4); (32,20); (258,36); (4240,5796);
                (191206,431453); (766241307,234444571);
                (2641033883877,339020201163)|] in
  let each_internal_expr str m =
    let module B = (val !bexpr: Expr) in
    let module M = MakeMain(B) in
    for i = 0 to m do
      printf "Trying -E %s %d ...@." str i;
      let start, cycle, _ = M.rho_check (B.expr_of_list [i]) in
      printf "Found! (%d = %d [%d])@." (start+cycle) start cycle;
      if (start, cycle) <> tests.(i) then begin
        eprintf "Incorrect at %d!@." i; exit 1
      end else
        printf "Correct.@."
    done in
  let run_algo (a,m) =
    algo := a;
    List.iter (fun (str,set_expr) ->
      set_expr();
      let m = match str with
        | "IS" | "DS" -> min m 3
        | "TS" -> min m 4
        | _ -> m in
      each_internal_expr str m) internal_expr_alist in
  List.iter run_algo [Naive, 3; Floyd, 4; Brent, 4;
                      Gosper, 4; Gosper2, 4];
  printf "All monomial tests are passed.@."
  

let string_of_int_list =
  let buf = Buffer.create 64 in
  fun l ->
  Buffer.reset buf;
  List.iter (fun i -> Buffer.add_string buf (" "^string_of_int i)) l;
  Buffer.contents buf

let run_polynomial_test upto =
  let test_lss = (* test inits with uppor bound for RB *)
    [[0;0], 500; [1;1;0], 447; [3;0;0], 499; [4;3], 422] in
  match internal_expr_alist with
  | [] -> failwith "internal_expr_alist: empty"
  | (str0, set_expr)::rest_alist ->
     let each_ls (ls,uptoRB) =
       let ls_str = string_of_int_list ls in
       printf "Computing -E %s %s ...@." str0 ls_str;
       set_expr();
       let module B = (val !bexpr: Expr) in
       let init = B.expr_of_list ls in
       let res = Array.make (upto+1) [] in
       let rec loop i e =
         res.(i) <- B.list_of_expr e;
         if i < upto then loop (succ i) (B.apply e init) in
       loop 1 (B.copy init);
       printf "Done.@.";
       List.iter (fun (str, set_expr) ->
         let upto = 
           match str with
           | "IS" | "DS" | "TS" -> 1
           | "RB" -> min uptoRB upto
           | _ -> upto in
         printf "Trying -E %s %s ...@." str ls_str;
         set_expr();
         let module B = (val !bexpr: Expr) in
         let init = B.expr_of_list ls in
         let rec loop i e =
           if B.list_of_expr e <> res.(i) then begin
               eprintf "Differs from %s at %d!@." str0 i; exit 1
             end;
           if i < upto then loop (succ i) (B.apply e init) in
         loop 1 (B.copy init);
         printf "Passed.@.") rest_alist in
     List.iter each_ls test_lss;
     printf "All polynomial tests are passed.@."

let rec add_spec keys spec doc speclist = match keys with
  | [] -> speclist
  | key::keys' -> add_spec keys' spec doc ((key,spec,doc)::speclist)
let rec add_speclist ks_spcl spcl = match ks_spcl with
  | [] -> Arg.align spcl
  | (keys,spec,doc)::rest ->
     add_speclist rest (add_spec keys spec (" "^doc) spcl)
let make_speclist ks_spcl = List.rev(add_speclist ks_spcl [])

let add_display hs = match !display with
  | Show l -> display := Show (hs::l)
  | _ -> display := Show [hs]

let speclist = make_speclist [
  ["-n"], Arg.Set_int limit,
  "Limit number of self applications (default = "^string_of_int !limit^")";
  ["-u" (*;"--unbound"*)],
  Arg.Unit(fun () -> limit := Pervasives.max_int-1),
  "Keep on trying self applications unless the rho-property is found";

  ["-q" (*;"--quiet"*)], Arg.Unit(fun () -> display := Quiet),
  "Quiet mode";
  ["-e" (*;"--every"*)], Arg.Int(fun i -> display := Every i),
  "Display only status every n";

  ["-m"(*;"--map"*)], Arg.Unit(fun () -> store := Map),
  "Use the Map module to store the history (in naive cycle detection)";

  ["-x" (*;"--extreamly-easy-run"*)],
  Arg.Unit(fun () ->
      display := Quiet;
      algo := Brent;
      limit := Pervasives.max_int-1;
      bexpr := (module ReuseBytes)),
  "Easy run mode for monomial cases equivalent to -q -u -b -E RB";

  ["-f";"--floyd"], Arg.Unit(fun () -> algo := Floyd),
  "Use Floyd's cycle-finding algorithm";
  ["-b";"--brent"], Arg.Unit(fun () -> algo := Brent),
  "Use Brent's cycle-finding algorithm";
  ["-g";"--gosper"], Arg.Unit(fun () -> algo := Gosper),
  "Use Gosper's cycle-finding algorithm";
  ["-g2"(*;"-gosper2"*)], Arg.Unit(fun () -> algo := Gosper2),
  "Use Improved Gosper's cycle-finding algorithm (efficient for very late cycles)";

  ["-r";"--restart"], Arg.String(fun s ->
                                if !algo = Naive then algo := Floyd;
                                restart_file := Some s),
  "Running with restartable mode (default: Floyd's cycle-finding algorithm)";
  ["-R";"--restart-auto"], Arg.Unit(fun () ->
                                   if !algo = Naive then algo := Floyd;
                                   restart_file := Some ""),
  "Similar to '-r' but with specifying no filename";
 
  ["-E"], Arg.Symbol(List.map fst internal_expr_alist,
                     fun s -> List.assoc s internal_expr_alist ()),
  "Select internal representation of decreasing polynomials";
  (* 
  "Select internal representation of decreasing polynomials\n"^
  "\tLL: List of the numbers of the same level for respective levels where all numbers <= 2^62-1 (e.g., [1;0;3] stands for 2.2.2.0)\n"^
  "\tBL: Byte string implementation of LL where all nubmers <= 255\n"^
  "\tRB (default): Reuse-as-much-as-possible version of BL\n"^
  "\tRL: Reversed list (e.g., [0;2;2;2] for 2.2.2.0)\n"^
  "\tZS: Binary notation as a composition of 0 (\\x.Bx) and 1 (\\x.BxB)";
   *)

  ["-w"(*;"-width"*)], Arg.Set_int wid,
  "Display each digit in the width";

  ["-S";"--sum"], Arg.Unit(fun () -> add_display Sum),
  "Display its sum";
  ["-L";"--length"], Arg.Unit(fun () -> add_display Length),
  "Display its length";
  ["-H";"--height"], Arg.Unit(fun () -> add_display Height),
  "Display its height (maximum level + 1)";
  ["-D";"--depth"], Arg.Unit(fun () -> add_display Depth),
  "Display its depth";
  ["-B";"--bar-chart"], Arg.Unit(fun () -> add_display BarChart),
  "Display as bar chart like histogram the further step of shrink potential";

  ["-V"], Arg.String(fun s -> add_display (Value s)),
  "Display its value computed by a given arithmetic expression where S (sum), L (length), H (height), and D (depth) are available. Try -V S -V H -V 'S+L'.";

  ["-t"], Arg.Unit(fun () ->
              run_monomial_test(); run_polynomial_test 500;
              printf "=> All tests are passed!@."; exit 0),
  "Test algorithms and internal expressions";

  (* override to hide default help messages *)
  ["-help";"--help"],
  Arg.Unit(fun () -> raise(Arg.Bad"")),
  " Display this list of options";

]

let usage_msg = "Usage: "^Sys.argv.(0)
let usage () = Arg.usage speclist usage_msg; exit 1
let anon_fun str = 
  try blist := int_of_string str :: !blist with _ -> usage ()

let () =
  Arg.parse speclist anon_fun usage_msg;
  if !blist = [] then usage ();
  let module B = (val !bexpr: Expr) in
  let module M = MakeMain(B) in
  M.main ()
