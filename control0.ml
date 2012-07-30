type ('a, 'r) cont = H of ('a -> 'r) * (('a -> 'r) -> 'r) | HV of 'r
type ('a, 'r) prop_prompt = (('a, 'r) cont) Delimcc.prompt

type 'r stop_prompt = 'r Delimcc.prompt

let hr_stop : 'r stop_prompt -> ('a, 'r) cont -> 'r =
  fun prompt ->
    function
      | (H (f, x)) -> Delimcc.push_prompt prompt (fun () -> x f)
      | (HV x)     -> x
let hs_stop = hr_stop

let hr_prop : ('a, 'r) prop_prompt -> ('a, 'r) cont -> 'r =
  fun _prompt ->
    function
      | (H (f, x)) -> x f
      | (HV x)     -> x

let rec hs_prop : ('a, 'r) prop_prompt -> ('a, 'r) cont -> 'r =
  fun prompt ->
    function
      | (H (f, x)) -> Delimcc.shift prompt (fun g -> H ((fun y -> hs_prop prompt (g (f y))), x))
      | (HV x)     -> x

let prompt0 : ('a, 'r) prop_prompt -> (unit -> 'r) -> 'r =
  fun prompt e ->
    hr_prop prompt (Delimcc.push_prompt prompt (fun () -> HV (e ())))
let control0 : ('a, 'r) prop_prompt -> (('a -> 'r) -> 'r) -> 'a =
  fun prompt c ->
    Delimcc.shift prompt (fun k -> H ((fun x -> hs_prop prompt (k x)), c))

let control0' : 'r stop_prompt -> (('a -> 'r) -> 'r) -> 'a =
  fun p f ->
    Delimcc.take_subcont p
      (fun sk () ->
         f (fun c -> Delimcc.push_subcont sk (fun () -> c)))
