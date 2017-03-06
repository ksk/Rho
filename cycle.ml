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
      else begin
        find_loop next1 next2 (succ i)
      end

  (* Find the entry of loop by starting with i such that e=A(i)=A(2i) *)
  (* and searching the smallest k with x = A(k) = A(i+k)              *)
  (* to return k and x                                                *)
  let rec find_loop_entry last1 last2 i e cnt =
    let next1 = E.next last1 in
    let next2 = E.next last2 in
    if E.equal next1 next2 then (i, cnt, next1)
    else
      let cnt = if E.equal e next2 then succ cnt else cnt in
      E.display i next1;
      find_loop_entry next1 next2 (succ i) e cnt

  let find_cycle init =
    (* Find (the smallest) i and e s.t. e = A(i) = A(2i) *)
    let i, e = find_loop init (E.next init) 2 in
    printf "Loop detected! (%d = %d [%d])@." (2*i) i i;
    (* Find (the smallest) k, c and x s.t. x = A(k) = A(i+k) 
       where c is 1 + the number of j satisfying e = A(j) and k < j < i+k *)
    let k, c, x = find_loop_entry init (E.next e) (succ i) e 1 in
    printf "Loop entry found at %d!@." (k-i+1);
    assert (i mod c = 0);
    let loop_size = i / c in
    k-i+1, loop_size
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
