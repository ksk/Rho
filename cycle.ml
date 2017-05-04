(* Finding cycles *)
open Format
open Store

module type ExprType = sig
  type t
  val limit : int
  val next  : t -> t
  val equal : t -> t -> bool
  val display : int -> t -> unit
end

(* (\* stores with numbers *\) *)
(* module type StoreType = sig *)
(*   type t *)
(*   type store *)
(*   (\* Return the correponding number if a given expression is found *\) *)
(*   val find      : t -> store -> int *)
(*   (\* Add a given expression to the store *\)                                     *)
(*   val add	: t -> int -> store -> store *)
(*   val singleton	: t -> int -> store *)
(* end *)

type restart = RBrent | RFloyd

module Naive (E:ExprType) (S:StoreType with type t = E.t) = struct
  type t = E.t
  let find_cycle init =
    let rec loop last i hist =
      if i > E.limit then begin
        if E.limit > 1 then printf "%d terms are all different.@." E.limit;
        exit 0
      end else
        let next = E.next last in
        try let prev = S.find next hist in
            (prev, i-prev)
        with Not_found ->
          E.display i next;
          loop next (i+1) (S.add next i hist) in
    E.display 1 init;
    loop init 2 (S.singleton init 1)
end

module Floyd (E:ExprType) = struct
  type t = E.t

  (* Find loop by Floyd's tortoise-and-hare cycle-finding algorithm *)
  (* to return i and e such that e = A(i) = A(2i)                   *)
  let rec find_loop last1 last2 i =
    if i > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (2 * E.limit);
      exit 0
    end else
      let next1 = E.next last1 in
      let next2 = E.next (E.next last2) in
      E.display i next1;
      (* E.display (2*i) next2; *)
      if E.equal next1 next2 then (i, next1)
      else find_loop next1 next2 (succ i)

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i e cyc_op =
    let next1 = E.next last1 in
    let next2 = E.next last2 in
    if E.equal next1 next2 then (i, cyc_op, next1)
    else
      let cyc_op = match cyc_op with
        | None when E.equal e next2 -> Some i
        | _ -> cyc_op in
      E.display i next1;
      find_loop_entry next1 next2 (succ i) e cyc_op

  let find_cycle init =
    E.display 1 init;
    (* Find (the smallest) i and e s.t. e = A(i) = A(2i) *)
    let i, e = find_loop init (E.next init) 2 in
    printf "Loop detected! (%d = %d [%d])@." (2*i) i i;
    (* Find (the smallest) k, c and x s.t. x = A(k) = A(i+k) 
       where c is A(c) = A(i) and i < c < 2i *)
    let k, co, x = find_loop_entry init (E.next e) (succ i) e None in
    let loop_size = match co with None -> i | Some c -> c-i+1 in
    printf "Loop entry found at %d!@." (k-i+1);
    k-i+1, loop_size
end

(* Restartable Floyd's cycle detection *) 
(* limit is unabled. *)
module RestartableFloyd (E:ExprType) = struct
  type t = E.t

  type funcall =
    | Init
    | FindLoop of { last1: t; last2: t; i: int }
    (* | FindLoopEntry of { last1: t; last2: t; i: int; e: t; cnt: int } *)
    | FindLoopEntry of { last1: t; last2: t; i: int; e: t; cyc_op: int option }
  type state = { mutable init: t option;
                 mutable i_e: (int * t) option; (* (i, A(i)) s.t. A(i)=A(2i) *)
                 mutable funcall: funcall;
                 mutable elapsed: float;
               }

  let state = { init = None; i_e = None; funcall = Init; elapsed = 0. }
  let stime = ref (Unix.gettimeofday()) (* start time *)
  let rfile = ref ""      (* the file name for restarting *)

  let save_current_state state =
    let elapsed = state.elapsed +. Unix.gettimeofday()-. !stime in
    state.elapsed <- elapsed;
    let oc = open_out !rfile in
    output_value oc (RFloyd, state);
    close_out oc

  exception Interrupted of state

  (* Find loop by Floyd's tortoise-and-hare cycle-finding algorithm *)
  (* to return i and e such that e = A(i) = A(2i)                   *)
  let rec find_loop last1 last2 i =
    state.funcall <- FindLoop{ last1; last2; i };
    let next1 = E.next last1 in
    let next2 = E.next (E.next last2) in
    E.display i next1;
    (* E.display (2*i) next2; *)
    if i land 0xffffff = 0 then save_current_state state;
    if E.equal next1 next2 then (i, next1)
    else find_loop next1 next2 (succ i)

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i e cyc_op =
    state.funcall <- FindLoopEntry{ last1; last2; i; e; cyc_op };
    let next1 = E.next last1 in
    let next2 = E.next last2 in
    if E.equal next1 next2 then (i, cyc_op, next1)
    else
      let cyc_op = match cyc_op with
        | None when E.equal e next2 -> Some i
        | _ -> cyc_op in
      E.display i next1;
      if i land 0xffffff = 0 then save_current_state state;
      find_loop_entry next1 next2 (succ i) e cyc_op

  let find_cycle_with_state init =
    E.display 1 init;
    (* Find (the smallest) i and e s.t. e = A(i) = A(2i) *)
    let i, e = match state.funcall with
      | Init -> find_loop init (E.next init) 2 
      | FindLoop { last1; last2; i } -> find_loop last1 last2 i
      | FindLoopEntry _ -> match state.i_e with
                           | None -> failwith "impossible state."
                           | Some i_e -> i_e in
    state.i_e <- Some(i,e);
    printf "Loop detected! (%d = %d [%d])@." (2*i) i i;
    (* Find (the smallest) k, c and x s.t. x = A(k) = A(i+k) 
       where c is A(c) = A(i) and i < c < 2i *)
    let k, co, x = match state.funcall with
      | Init | FindLoop _ ->
         find_loop_entry init (E.next e) (succ i) e None
      | FindLoopEntry { last1; last2; i; e; cyc_op } ->
         find_loop_entry last1 last2 i e cyc_op in
    let loop_size = match co with None -> i | Some c -> c-i+1 in
    printf "Loop entry found at %d!@." (k-i+1);
    k-i+1, loop_size

  let find_cycle_restart expr fname =
    let auto, fname =
      if fname = "" then true, sprintf ".bfloyd%d" (Hashtbl.hash expr)
      else false, fname in
    rfile := fname;
    stime := Unix.gettimeofday();
    Sys.(set_signal sigint
           (Signal_handle(fun _signum -> raise (Interrupted state))));
    (* Load a state from a given file *)
    let restart, {init; i_e; funcall; elapsed} =
      try input_value (open_in fname)
      with _ -> RFloyd, { init = Some expr; i_e = None; funcall = Init;
                          elapsed = 0. } in
    if restart <> RFloyd then
      begin eprintf"Inconsistent cycle detection mode.@."; exit 1 end;
    state.init <- init; state.i_e <- i_e; state.funcall <- funcall;
    state.elapsed <- elapsed;
    if state.init <> Some expr then
      begin eprintf"inconsistent initial expression."; exit 1 end;
    let init = match state.init with None -> expr | Some e -> e in
    try
      let res = find_cycle_with_state init in
      let elapsed = state.elapsed +. Unix.gettimeofday()-. !stime in
      begin try Unix.unlink fname with _ -> () end;
      eprintf "Elapsed time: %.3f sec@." elapsed;
      res
    with Interrupted state ->
      save_current_state state;
         let funcall = match state.funcall with
           | Init -> "init"
           | FindLoop { i } -> sprintf "find_loop _ _ %d" i
           | FindLoopEntry { i } -> sprintf "find_loop_entry _ _ %d _ _" i in
         let opt_r = if auto then "-R" else sprintf "-r %s" !rfile in
         eprintf ("Interrupted at '%s' (%.2f sec).@."
                  ^^"You can run again with '%s'.@.")
                 funcall state.elapsed opt_r;
         exit 0

end

(* Sample

  module E = struct 
    type t = int
    let limit = 100
    let next i = if i > 26 then 23 else i+1
    let equal = (=)
    let display i e = printf "%d => %d; " i e
  end

  module R = Rho(E)

  let start, cycle = R.find_cycle 6

*)

(* Brent's algorithm *)
module Brent (E:ExprType) = struct
  type t = E.t

  (* Find loop by Brent's cycle-finding algorithm                    *)
  (* to return k and pow such that A(pow=2**n) = A(pow+k) (1<=k<pow) *)
  let rec find_loop last1 last2 i pow =
    if pow > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (pow+i);
      exit 0
    end else
      if E.equal last1 last2 then (i,pow)
      else 
        let next2 = E.next last2 in
        E.display (pow+i+1) next2;
        if i = pow then
          find_loop last2 next2 1 (pow lsl 1)
        else
          find_loop last1 next2 (succ i) pow
                    
  let rec find_kth x1 k =
    if k <= 1 then x1 else find_kth (E.next x1) (k-1)

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i =
    if E.equal last1 last2 then (i, last1)
    else
      let next1 = E.next last1 in
      let next2 = E.next last2 in
      E.display (succ i) next1;
      find_loop_entry next1 next2 (succ i)

  let find_cycle init =
    E.display 1 init;
    let next = E.next init in
    E.display 2 next;
    (* Find (the smallest) c and e s.t. e = A(i) = A(i+c) with i=2**j-1 
       with smallest j  *)
    let loop_size, pow = find_loop init next 1 1 in
    printf "Loop detected! (%d = %d [%d])@." (pow+loop_size) pow loop_size;
    (* Compute A(c) *)
    let e = find_kth init loop_size in
    (* Find (the smallest) k and x s.t. x = A(k) = A(k+c) *)
    let k, x = find_loop_entry init (E.next e) 1 in
    printf "Loop entry found at %d!@." k;
    k, loop_size
end

(* Restartable Brent's algorithm *)
module RestartableBrent (E:ExprType) = struct
  type t = E.t

  type funcall =
    | Init
    | FindLoop of { last1: t; last2: t; i: int; pow: int }
    | FindKth of { x1: t; k: int }
    | FindLoopEntry of { last1: t; last2: t; i: int }

  type state = { mutable init: t option;
                 mutable find_loop: (int * int) option;
                 mutable find_kth: t option;
                 mutable funcall: funcall;
                 mutable elapsed: float; }

  exception Interrupted of state

  let state = { init = None;
                find_loop = None;
                find_kth = None;
                funcall = Init;
                elapsed = 0.  }
  let stime = ref (Unix.gettimeofday()) (* start time *)
  let rfile = ref ""      (* the file name for restarting *)

  let save_current_state state =
    let elapsed = state.elapsed +. Unix.gettimeofday() -. !stime in
    state.elapsed <- elapsed;
    let oc = open_out !rfile in
    output_value oc (RBrent, state);
    close_out oc

  (* Find loop by Brent's cycle-finding algorithm                    *)
  (* to return k and pow such that A(pow=2**n) = A(pow+k) (1<=k<pow) *)
  let rec find_loop last1 last2 i pow =
    state.funcall <- FindLoop { last1; last2; i; pow };
    if pow > E.limit then begin
      if E.limit > 1 then
        eprintf "%d terms are all different.@." (pow+i);
      exit 0
    end else
      if E.equal last1 last2 then (i,pow)
      else 
        let next2 = E.next last2 in
        E.display (pow+i+1) next2;
        if i land 0xffffff = 0 then save_current_state state;
        if i = pow then
          find_loop last2 next2 1 (pow lsl 1)
        else
          find_loop last1 next2 (succ i) pow
                    
  let rec find_kth x1 k =
    state.funcall <- FindKth { x1; k };
    if k <= 1 then x1 else find_kth (E.next x1) (k-1)

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i =
    state.funcall <- FindLoopEntry { last1; last2; i };
    if E.equal last1 last2 then (i, last1)
    else
      let next1 = E.next last1 in
      let next2 = E.next last2 in
      E.display i next1;
      if i land 0xffffff = 0 then save_current_state state;
      find_loop_entry next1 next2 (succ i)

  let find_cycle_with_funcall init =
    E.display 1 init;
    begin match state.init with
          | Some e -> 
              if e <> init then
                begin eprintf"inconsistent initial expression."; exit 1 end
          | None -> state.init <- Some init end;
    let next = E.next init in
    E.display 2 next;
    (* Find (the smallest) c and e s.t. e = A(i) = A(i+c) with i=2**j-1 
       with smallest j *)
    let loop_size, pow = match state.funcall with
      | Init -> find_loop init next 1 1
      | FindLoop{last1;last2;i;pow} -> find_loop last1 last2 i pow
      | _ -> match state.find_loop with
             | None -> invalid_arg "wrong state (find_loop)"
             | Some ls_p -> ls_p in
    state.find_loop <- Some(loop_size, pow);
    printf "Loop detected! (%d = %d [%d])@." (pow+loop_size) pow loop_size;
    (* Compute A(c) *)
    let e = match state.funcall with
      | Init | FindLoop _ -> find_kth init loop_size
      | FindKth{x1;k} -> find_kth x1 k
      | _ -> match state.find_kth with
             | None -> invalid_arg "wrong state (find_kth)"
             | Some e -> e in
    state.find_kth <- Some e;
    (* Find (the smallest) k and x s.t. x = A(k) = A(k+c) *)
    let k, x = match state.funcall with
      | Init | FindLoop _ | FindKth _ -> find_loop_entry init (E.next e) 1
      | FindLoopEntry{last1;last2;i} -> find_loop_entry last1 last2 i in
    printf "Loop entry found at %d!@." k;
    k, loop_size

  let find_cycle_restart init fname =
    (* generate a filename if specifying no fileneme *)
    let auto, fname =
      if fname = "" then true, sprintf ".bbrent%d" (Hashtbl.hash init)
      else false, fname in
    rfile := fname;
    stime := Unix.gettimeofday();
    Sys.(set_signal sigint
           (Signal_handle(fun _signum -> raise (Interrupted state))));
    (* Load a state from a given file *)
    let restart, s =
      try input_value (open_in !rfile) with _ -> RBrent, state in
    state.init <- s.init; state.find_loop <- s.find_loop;
    state.find_kth <- s.find_kth; state.funcall <- s.funcall;
    state.elapsed <- s.elapsed;
    if restart <> RBrent then
      begin eprintf"Inconsistent cycle detection mode.@."; exit 1 end;
    try 
      let res = find_cycle_with_funcall init in
      let elapsed = state.elapsed+.Unix.gettimeofday()-. !stime in
      begin try Unix.unlink !rfile with _ -> () end;
      eprintf "Elapsed time: %.3f sec@." elapsed;
      res
    with Interrupted state ->
      save_current_state state;
      let funcall = match state.funcall with
        | Init -> "init"
        | FindLoop { i; pow } -> sprintf "find_loop _ _ %d %d" i pow
        | FindKth { k } -> sprintf "find_kth _ %d" k
        | FindLoopEntry { i } -> sprintf "find_loop_entry _ _ %d" i in
      let opt_r = if auto then "-R" else sprintf "-r %s" !rfile in
      eprintf ("Interrupted at '%s' (%.2f sec).@."
               ^^"You can run again with '%s'.@.")
              funcall state.elapsed opt_r;
      exit 0
end
