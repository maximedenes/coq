let max_array_length32 = 18014398509481983
(* 4194303 Sys.max_array_length on arch32 *)

let length_to_int i = snd (Uint63.to_int2 i) (* TODO check correctness on 32 bits *)

let trunc_size n =
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int max_array_length32) then
    length_to_int n + 1
  else max_array_length32

type 'a t = ('a kind) ref
and 'a kind =
  | Array of 'a array
        (* | Matrix of 'a array array *)
  | Updated of int * 'a * 'a t

let of_array t = ref (Array t)

let debug s = if !Flags.debug then Feedback.msg_debug Pp.(str s) (* TODO remove *)

let rec length p =
  match !p with
  | Array t -> Uint63.of_int (Array.length t - 1) (* The default value *)
  | Updated (_, _, p) -> length p

let length p =
  match !p with
  | Array t -> Uint63.of_int (Array.length t - 1)
  | Updated (_, _, p) -> debug "Array.length"; length p

let rec get_updated p n =
  match !p with
  | Array t ->
      let l = Array.length t in
      if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
        Array.unsafe_get t (length_to_int n)
      else (debug "Array.get: out of bound";Array.unsafe_get t (l-1))
  | Updated (k,e,p) ->
     if Uint63.equal n (Uint63.of_int k) then e
     else get_updated p n

let get p n =
  match !p with
  | Array t ->
      let l = Array.length t in
      if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
        Array.unsafe_get t (length_to_int n)
      else (debug "Array.get: out of bound";Array.unsafe_get t (l-1))
  | Updated _ -> debug "Array.get";get_updated p n

let set p n e =
  let kind = !p in
  match kind with
  | Array t ->
      let l = Uint63.of_int (Array.length t - 1) in
      if Uint63.le Uint63.zero n && Uint63.lt n l then
        let res = ref kind in
        let n = length_to_int n in
        p := Updated (n, Array.unsafe_get t n, res);
        Array.unsafe_set t n e;
        res
      else (debug "Array.set: out of bound"; p)
  | Updated _ ->
      debug "Array.set";
      if Uint63.le Uint63.zero n && Uint63.lt n (length p) then
        ref (Updated((length_to_int n), e, p))
      else (debug "Array.set: out of bound"; p)

let destr_set p n e =
  let kind = !p in
  match kind with
  | Array t ->
      let l = Uint63.of_int (Array.length t - 1) in
      if Uint63.le Uint63.zero n && Uint63.lt n l then
        let n = length_to_int n in
        Array.unsafe_set t n e;
        p
      else (debug "Array.set: out of bound"; p)
  | Updated _ -> set p n e

let rec default_updated p =
  match !p with
  | Array t -> Array.unsafe_get t (Array.length t - 1)
  | Updated (_,_,p) -> default_updated p

let default p =
  match !p with
  | Array t -> Array.unsafe_get t (Array.length t - 1)
  | Updated (_,_,p) -> debug "Array.default";default_updated p

let make n def =
  ref (Array (Array.make (trunc_size n) def))

let init n f def =
  let n = trunc_size n in
  let t = Array.make n def in
  for i = 0 to n - 2 do Array.unsafe_set t i (f i) done;
  ref (Array t)

let rec copy_updated p =
  match !p with
  | Array t -> Array.copy t
  | Updated (n,e,p) ->
      let t = copy_updated p in
      Array.unsafe_set t n e; t

let to_array p =
  match !p with
  | Array t -> Array.copy t
  | Updated _ -> debug "Array.copy"; copy_updated p

let copy p = ref (Array (to_array p))

let rec rerootk t k =
  match !t with
  | Array _ -> k ()
  | Updated (i, v, t') ->
      let k' () =
        begin match !t' with
        | Array a as n ->
            let v' = a.(i) in
            Array.unsafe_set a i v;
            t := n;
            t' := Updated (i, v', t)
        | Updated _ -> assert false
        end; k() in
      rerootk t' k'

let reroot t = rerootk t (fun () -> t)

let map f p =
  match !p with
  | Array t -> ref (Array (Array.map f t))
  | _ ->
      let len = length_to_int (length p) in
      ref (Array
             (Array.init (len + 1)
                (fun i -> f (get p (Uint63.of_int i)))))
