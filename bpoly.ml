open Format
open Store
open Cycle
open Bexpr

let limit = ref 65535
type howshow = Sum | Length | Height | Depth | BarChart
type algo = Naive | Floyd | Brent | Gosper
type store = Map | Hashtbl
type display = Quiet | Verbose | Every of int | Show of howshow list

let restart_file : string option ref = ref None
let algo = ref Naive
let store = ref Hashtbl
let bexpr = ref (module PureBytes: Expr)
let display = ref Verbose
let blist = ref []
let wid = ref 1

let show_algo algo_str =
  printf "Cycle detection algorithm: %s@." algo_str

module type Main = sig
  val main: unit -> unit
end

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

  module type EStoreType = StoreType with type t = B.t

  let make_stmod = function
    | Map -> (module MakeMapStore(B) : EStoreType)
    | Hashtbl -> (module MakeHashtblStore(B) : EStoreType)      
                         
  let rho_check_naive stmod expr =
    let next_impure =
      if expr_length expr = 1 then
        let h = expr_height expr-1 in
        (fun e -> B.apply_mono e h) 
      else
        (fun e -> B.apply e expr) in
    let module N =
      (Naive (struct
           type t = B.t
           let limit = !limit
           let next_impure = next_impure
           let next e = next_impure (B.copy e)
           let copy x = B.copy x
           let equal = B.equal
           let display = show_status !display
         end) ((val stmod : EStoreType))) in
    N.find_cycle expr
    
  let rho_check_floyd expr =
    let next_impure =
      if expr_length expr = 1 then
        let h = expr_height expr-1 in
        (fun e -> B.apply_mono e h) 
      else
        (fun e -> B.apply e expr) in
    let module R =
      (Floyd (struct
           type t = B.t
           let limit = !limit
           let next_impure = next_impure
           let next e = next_impure (B.copy e)
           let copy x = B.copy x
           let equal = B.equal
           let display = show_status !display
         end)) in
    R.find_cycle expr
    
  let rho_check_brent expr =
    let next_impure =
      if expr_length expr = 1 then
        let h = expr_height expr-1 in
        (fun e -> B.apply_mono e h)
      else
        (fun e -> B.apply e expr) in
    let module R =
      (Brent (struct
           type t = B.t
           let limit = !limit
           let next_impure = next_impure
           let next e = next_impure (B.copy e)
           let copy x = B.copy x
           let equal = B.equal
           let display = show_status !display
         end)) in
    R.find_cycle expr

  let rho_check_gosper expr =
    let next_impure =
      if expr_length expr = 1 then
        let h = expr_height expr-1 in
        (fun e -> B.apply_mono e h)
      else
        (fun e -> B.apply e expr) in
    let module R =
      (Gosper (struct
           type t = B.t
           let limit = !limit
           let next_impure = next_impure
           let next e = next_impure (B.copy e)
           let copy x = B.copy x
           let equal = B.equal
           let display = show_status !display
         end)) in
    R.find_cycle expr
    
  let rho_check_restart_floyd expr fname =
    let module R =
      (RestartableFloyd (struct
           type t = B.t
           let limit = !limit
           let next e = B.apply (B.copy e) expr
           let next_impure x = next x
           let copy x = B.copy x
           let equal = (=)
           let display = show_status !display
         end)) in
    R.find_cycle_restart expr fname
    
  let rho_check_restart_brent expr fname =
    let module R =
      (RestartableBrent (struct
           type t = B.t
           let limit = !limit
           let next e = B.apply (B.copy e) expr
           let next_impure x = next x
           let copy x = B.copy x
           let equal = (=)
           let display = show_status !display
         end)) in
    R.find_cycle_restart expr fname
    
  let rho_check_restart_gosper expr fname =
    let module R =
      (RestartableGosper (struct
           type t = B.t
           let limit = !limit
           let next e = B.apply (B.copy e) expr
           let next_impure x = next x
           let copy x = B.copy x
           let equal = (=)
           let display = show_status !display
         end)) in
    R.find_cycle_restart expr fname

  let rho_check expr = match !algo with
    | Naive ->
       let stmod = make_stmod !store in
       show_algo "Naive";
       rho_check_naive stmod expr
    | Floyd ->
       begin match !restart_file with
             | None ->
                show_algo "Floyd";
                rho_check_floyd expr
             | Some fname ->
                show_algo "Restartable (Floyd)";
                rho_check_restart_floyd expr fname end
    | Brent ->
       begin match !restart_file with
             | None ->
                show_algo "Brent";
                rho_check_brent expr
             | Some fname ->
                show_algo "Restartable (Brent)";
                rho_check_restart_brent expr fname end
    | Gosper ->
       match !restart_file with
             | None ->
                show_algo "Gosper";
                rho_check_gosper expr
             | Some fname ->
                eprintf "Restartable (Gosper): not implemented yet@.";
                exit 1
                (*
                  show_algo "Restartable (Gosper)";
                  rho_check_restart_gosper expr fname *)

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

let rec add_spec keys spec doc speclist = match keys with
  | [] -> speclist
  | key::keys' -> add_spec keys' spec doc ((key,spec,doc)::speclist)
let rec add_speclist ks_spcl spcl = match ks_spcl with
  | [] -> Arg.align spcl
  | (keys,spec,doc)::rest -> add_speclist rest (add_spec keys spec (" "^doc) spcl)
let make_speclist ks_spcl = add_speclist ks_spcl []

let add_display hs = match !display with
  | Show l -> display := Show (hs::l)
  | _ -> display := Show [hs]

let speclist = make_speclist [
  ["-n"], Arg.Set_int limit,
  "Limit number of self applications (default = "^string_of_int !limit^")";
  ["-u";"-unbound"], Arg.Unit(fun () -> limit := Pervasives.max_int-1),
  "Keep on trying self applications unless the rho-property is found";

  ["-q";"-quiet"], Arg.Unit(fun () -> display := Quiet),
  "Quiet mode";
  ["-e";"-every"], Arg.Int(fun i -> display := Every i),
  "Display only status every n";

  ["-mm";"-map"], Arg.Unit(fun () -> store := Map),
  "Use the Map module to store the history (in naive cycle detection)";

  ["-E";"-exp"], Arg.String(fun e ->
                     let module B = (val match e with
                     | "IS" -> (module IntBitSeq) (* DO NOT USE *)
                     | "DS" -> (module DIntBitSeq)
                     | "ZS" -> (module ZBitSeq)
                     | "ZB" -> (module ZBytes)
                     | "PB" -> (module PureBytes)
                     | "IB" -> (module ImpureBytes)
                     | "RL" -> (module RevList)
                     | "LL" -> (module LevelList)
                     | _ -> raise (Arg.Bad "Unknown internal representation mode"): Expr) in
                     bexpr := (module B)),
  "Select internal representation of decreasing polynomials (ZS|ZB|PB|IB";

  ["-f";"-floyd"], Arg.Unit(fun () -> algo := Floyd),
  "Use Floyd's cycle-finding algorithm";
  ["-b";"-brent"], Arg.Unit(fun () -> algo := Brent),
  "Use Brent's cycle-finding algorithm";

  ["-g";"-gosper"], Arg.Unit(fun () -> algo := Gosper),
  "Use Gosper's cycle-finding algorithm";
  ["-r";"-restart"], Arg.String(fun s ->
                                if !algo = Naive then algo := Floyd;
                                restart_file := Some s),
  "Running with restartable mode (default: Floyd's cycle-finding algorithm)";
  ["-R";"-restart-auto"], Arg.Unit(fun () ->
                                   if !algo = Naive then algo := Floyd;
                                   restart_file := Some ""),
  "Similar to '-r' but with specifying no filename";
 
  ["-w";"-width"], Arg.Set_int wid,
  "Display each digit in the width";

  ["-S";"-sum"], Arg.Unit(fun () -> add_display Sum),
  "Display its sum";
  ["-L";"-length"], Arg.Unit(fun () -> add_display Length),
  "Display its length";
  ["-H";"-height"], Arg.Unit(fun () -> add_display Height),
  "Display its height";
  ["-D";"-depth"], Arg.Unit(fun () -> add_display Depth),
  "Display its depth";
  ["-B";"-bar-chart"], Arg.Unit(fun () -> add_display BarChart),
  "Display as bar chart like histogram the further step of shrink potential";

]

let usage_msg = "Usage: "^Sys.argv.(0)
let usage () = Arg.usage speclist usage_msg; exit 1
let anon_fun str = 
  try blist := int_of_string str :: !blist with _ -> usage ()

let () =
  Arg.parse speclist anon_fun usage_msg;
  if !blist = [] then usage ();
  let module B = (val !bexpr: Expr) in
  let module M = (val (module MakeMain(B)): Main) in
  M.main ()
