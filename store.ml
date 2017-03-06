(* Stores for naive cycle detection *)

(* stores with numbers *)
module type StoreType = sig
  type t
  type store
  (* Return the correponding number if a given expression is found *)
  val find      : t -> store -> int
  (* Add a given expression to the store *)                                    
  val add	: t -> int -> store -> store
  val singleton	: t -> int -> store
end

module MakeMapStore(Ord: Map.OrderedType) = struct
  module M = Map.Make(Ord)             
  type t = M.key
  type store = int M.t
  let find = M.find
  let add = M.add
  let singleton = M.singleton
end

module MakeHashtblStore(H: Hashtbl.HashedType) = struct
  module T = Hashtbl.Make(H)
  type t = T.key
  type store = int T.t
  let find k t = T.find t k
  let add k v t = T.add t k v; t
  let singleton k v =
    let t = T.create (1 lsl 20 + 1) in
    T.add t k v;
    t
end




