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
                 mutable funcall: funcall }

  let state = { init = None; i_e = None; funcall = Init }
  exception Interrupted of state

  (* Find loop by Floyd's tortoise-and-hare cycle-finding algorithm *)
  (* to return i and e such that e = A(i) = A(2i)                   *)
  let rec find_loop last1 last2 i =
    state.funcall <- FindLoop{ last1; last2; i };
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
    state.funcall <- FindLoopEntry{ last1; last2; i; e; cyc_op };
    let next1 = E.next last1 in
    let next2 = E.next last2 in
    if E.equal next1 next2 then (i, cyc_op, next1)
    else
      let cyc_op = match cyc_op with
        | None when E.equal e next2 -> Some i
        | _ -> cyc_op in
      E.display i next1;
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
      if fname = "" then true, sprintf ".blist%d" (Hashtbl.hash expr)
      else false, fname in
    let stime = Unix.gettimeofday() in
    Sys.(set_signal sigint
           (Signal_handle(fun _signum -> raise (Interrupted state))));
    (* Load a state from a given file *)
    let elapsed, {init; i_e; funcall} =
      try input_value (open_in fname)
      with _ -> 0., { init = Some expr; i_e = None; funcall = Init } in
    state.init <- init; state.i_e <- i_e; state.funcall <- funcall;
    if state.init <> Some expr then
      begin eprintf"inconsistent initial expression."; exit 1 end;
    let init = match state.init with None -> expr | Some e -> e in
    try
      let res = find_cycle_with_state init in
      let elapsed = elapsed+.Unix.gettimeofday()-.stime in
      begin try Unix.unlink fname with _ -> () end;
      eprintf "Elapsed time: %.3f sec@." elapsed;
      res
    with Interrupted state ->
         let elapsed = elapsed+.Unix.gettimeofday()-.stime in
         output_value (open_out fname) (elapsed, state);
         let funcall = match state.funcall with
           | Init -> "init"
           | FindLoop { i } -> sprintf "find_loop _ _ %d" i
           | FindLoopEntry { i } -> sprintf "find_loop_entry _ _ %d _ _" i in
         let opt_r = if auto then "-R" else sprintf "-r %s" fname in
         eprintf ("Interrupted at '%s' (%.2f sec).@."
                  ^^"You can run again with '%s'.@.")
                 funcall elapsed opt_r;
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
      E.display i next1;
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

