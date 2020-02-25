let max_array_length32 = 4194303

let max_length = Uint63.of_int max_array_length32

let length_to_int i = snd (Uint63.to_int2 i) (* TODO check correctness on 32 bits *)

let trunc_size n =
  if Uint63.le Uint63.zero n && Uint63.lt n max_length then
    length_to_int n
  else max_array_length32

type 'a t = ('a kind) ref
and 'a kind =
  | Array of 'a array * 'a
  | Updated of int * 'a * 'a t

let unsafe_of_array t def = ref (Array (t,def))
let of_array t def = unsafe_of_array (Array.copy t) def

let debug s = if !Flags.debug then Feedback.msg_debug Pp.(str s) (* TODO remove *)

let rec length p =
  match !p with
  | Array (t,_) -> Uint63.of_int @@ Array.length t
  | Updated (_, _, p) -> length p

let length p =
  match !p with
  | Array (t,_) -> Uint63.of_int @@ Array.length t
  | Updated (_, _, p) -> debug "Array.length"; length p

let rec get_updated p n =
  match !p with
  | Array (t,def) ->
      let l = Array.length t in
      if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
        Array.unsafe_get t (length_to_int n)
      else (debug "Array.get: out of bound"; def)
  | Updated (k,e,p) ->
     if Uint63.equal n (Uint63.of_int k) then e
     else get_updated p n

let get p n =
  match !p with
  | Array (t,def) ->
      let l = Array.length t in
      if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
        Array.unsafe_get t (length_to_int n)
      else (debug "Array.get: out of bound"; def)
  | Updated _ -> debug "Array.get";get_updated p n

let set p n e =
  let kind = !p in
  match kind with
  | Array (t,_) ->
      let l = Uint63.of_int @@ Array.length t in
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
  | Array (t,_) ->
      let l = Uint63.of_int @@ Array.length t in
      if Uint63.le Uint63.zero n && Uint63.lt n l then
        let n = length_to_int n in
        Array.unsafe_set t n e;
        p
      else (debug "Array.set: out of bound"; p)
  | Updated _ -> set p n e

let rec default_updated p =
  match !p with
  | Array (_,def) -> def
  | Updated (_,_,p) -> default_updated p

let default p =
  match !p with
  | Array (_,def) -> def
  | Updated (_,_,p) -> debug "Array.default";default_updated p

let make n def =
  ref (Array (Array.make (trunc_size n) def, def))

let init n f def =
  let n = trunc_size n in
  let t = Array.init n f in
  ref (Array (t, def))

let rec copy_updated p =
  match !p with
  | Array (t,def) -> Array.copy t, def
  | Updated (n,e,p) ->
      let (t,_) as r = copy_updated p in
      Array.unsafe_set t n e; r

let to_array p =
  match !p with
  | Array (t,def) -> Array.copy t, def
  | Updated _ -> debug "Array.copy"; copy_updated p

let copy p =
  let (t,def) = to_array p in
  ref (Array (t,def))

let rec rerootk t k =
  match !t with
  | Array _ -> k ()
  | Updated (i, v, t') ->
      let k' () =
        begin match !t' with
        | Array (a,_def) as n ->
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
  | Array (t,def) -> ref (Array (Array.map f t, f def))
  | _ ->
      let len = length_to_int (length p) in
      let t = Array.init len (fun i -> f (get p (Uint63.of_int i))) in
      ref (Array(t, f (default p)))
