module Util = struct
  let split_path target =
    let split_target target =
      match target with
      | "" | "/" -> []
      | _ ->
        (match String.split_on_char '/' target with
         | "" :: xs -> xs
         | xs -> xs)
    in
    match String.index_opt target '?' with
    | None -> split_target target
    | Some 0 -> []
    | Some i -> split_target (String.sub target 0 i)
  ;;
end

module PatternTrie = struct
  module Key = struct
    type t =
      | Match : string -> t
      | Capture : t
      | Wildcard : t
  end

  module KeyMap = Map.Make (String)

  type 'a node =
    { parsers : 'a list
    ; children : 'a node KeyMap.t
    ; capture : 'a node option
    ; wildcard : bool
    }

  type 'a t = 'a node

  exception IncompatibleWildcard

  let empty = { parsers = []; children = KeyMap.empty; capture = None; wildcard = false }

  let feed_params t params =
    let rec aux t params =
      match t, params with
      | { parsers = []; _ }, [] -> []
      | { parsers = rs; _ }, [] -> rs
      | { parsers = rs; _ }, [ "" ] -> rs
      | { parsers = rs; wildcard; _ }, _ when wildcard -> rs
      | { children; capture; _ }, x :: xs ->
        (match KeyMap.find_opt x children with
         | None ->
           (match capture with
            | None -> []
            | Some t' -> aux t' xs)
         | Some m' -> aux m' xs)
    in
    aux t params
  ;;

  let add k v t =
    let rec aux k t =
      match k, t with
      | [], ({ parsers = x; wildcard; _ } as n) ->
        if wildcard then raise IncompatibleWildcard else { n with parsers = v :: x }
      | x :: r, ({ parsers; children; capture; wildcard; _ } as n) ->
        (match x with
         | Key.Match w ->
           if wildcard then raise IncompatibleWildcard;
           let t' =
             match KeyMap.find_opt w children with
             | None -> empty
             | Some v -> v
           in
           let t'' = aux r t' in
           { n with children = KeyMap.add w t'' children }
         | Key.Capture ->
           if wildcard then raise IncompatibleWildcard;
           let t' =
             match capture with
             | None -> empty
             | Some v -> v
           in
           let t'' = aux r t' in
           { n with capture = Some t'' }
         | Key.Wildcard ->
           if wildcard || (parsers = [] && KeyMap.is_empty children && capture = None)
           then { n with parsers = v :: parsers; wildcard = true }
           else raise IncompatibleWildcard)
    in
    aux k t
  ;;

  let rec union t1 t2 =
    let parsers = t1.parsers @ t2.parsers in
    let children =
      KeyMap.merge
        (fun _ l r ->
           match l, r with
           | None, None -> assert false
           | None, Some r -> Some r
           | Some l, None -> Some l
           | Some l, Some r -> Some (union l r))
        t1.children
        t2.children
    in
    let capture =
      match t1.capture, t2.capture with
      | None, None -> None
      | Some l, None -> Some l
      | None, Some r -> Some r
      | Some l, Some r -> Some (union l r)
    in
    let wildcard =
      match t1.wildcard, t2.wildcard with
      | false, false -> false
      | true, true -> true
      | false, true | true, false -> raise IncompatibleWildcard
    in
    { parsers; children; capture; wildcard }
  ;;
end

type 'a conv =
  { to_ : 'a -> string
  ; from_ : string -> 'a option
  ; label : string
  }

let conv to_ from_ label = { to_; from_; label }

module Parts = struct
  type t =
    { prefix : string list
    ; matched : string list
    }

  let of_parts' xs = { prefix = []; matched = xs }
  let of_parts x = of_parts' @@ Util.split_path x
  let wildcard_match t = String.concat "/" ("" :: t.matched)
  let prefix t = String.concat "/" ("" :: t.prefix)
end

type ('a, 'b) path =
  | End : ('a, 'a) path
  | Wildcard : (Parts.t -> 'a, 'a) path
  | Match : string * ('a, 'b) path -> ('a, 'b) path
  | Conv : 'c conv * ('a, 'b) path -> ('c -> 'a, 'b) path

type 'b route = Route : ('a, 'c) path * 'a * ('c -> 'b) -> 'b route
type 'b router =
  | TrieRouter of 'b route PatternTrie.t
  | UnionRouter of 'b router list

let pattern to_ from_ label r = Conv (conv to_ from_ label, r)
let custom ~serialize:to_ ~parse:from_ ~label r = Conv (conv to_ from_ label, r)
let empty_router = TrieRouter PatternTrie.empty
let ( @--> ) r handler = Route (r, handler, fun x -> x)
let route r handler = Route (r, handler, fun x -> x)
let s w r = Match (w, r)
let of_conv conv r = Conv (conv, r)
let int r = of_conv (conv string_of_int int_of_string_opt ":int") r
let int64 r = of_conv (conv Int64.to_string Int64.of_string_opt ":int64") r
let int32 r = of_conv (conv Int32.to_string Int32.of_string_opt ":int32") r
let str r = of_conv (conv (fun x -> x) (fun x -> Some x) ":string") r
let bool r = of_conv (conv string_of_bool bool_of_string_opt ":bool") r
let wildcard = Wildcard
let ( / ) m1 m2 r = m1 @@ m2 r
let nil = End
let ( /? ) m1 m2 = m1 m2

let rec route_pattern : type a b. (a, b) path -> PatternTrie.Key.t list = function
  | End -> []
  | Wildcard -> [ PatternTrie.Key.Wildcard ]
  | Match (w, fmt) -> PatternTrie.Key.Match w :: route_pattern fmt
  | Conv (_, fmt) -> PatternTrie.Key.Capture :: route_pattern fmt
;;

let pp_path' path =
  let rec aux : type a b. (a, b) path -> string list = function
    | End -> []
    | Wildcard -> [ ":wildcard" ]
    | Match (w, fmt) -> w :: aux fmt
    | Conv ({ label; _ }, fmt) -> label :: aux fmt
  in
  aux path
;;

let pp_target fmt t = Format.fprintf fmt "%s" ("/" ^ String.concat "/" @@ pp_path' t)
let string_of_path t = Format.asprintf "%a" pp_target t
let pp_route fmt (Route (p, _, _)) = pp_target fmt p
let string_of_route r = Format.asprintf "%a" pp_route r

let ksprintf' k path =
  let rec aux : type a b. (string list -> b) -> (a, b) path -> a =
    fun k -> function
      | End -> k []
      | Wildcard -> fun { Parts.matched; _ } -> k (List.concat [ matched; [] ])
      | Match (w, fmt) -> aux (fun s -> k @@ (w :: s)) fmt
      | Conv ({ to_; _ }, fmt) -> fun x -> aux (fun rest -> k @@ (to_ x :: rest)) fmt
  in
  aux k path
;;

let ksprintf k t = ksprintf' (fun x -> k ("/" ^ String.concat "/" x)) t
let sprintf t = ksprintf (fun x -> x) t

type 'a match_result =
  | FullMatch of 'a
  | MatchWithTrailingSlash of 'a
  | NoMatch

let parse_route path handler params =
  let rec match_target
    : type a b. (a, b) path -> a -> string list -> string list -> b match_result
    =
    fun t f seen s ->
    match t with
    | End ->
      (match s with
       | [ "" ] -> MatchWithTrailingSlash f
       | [] -> FullMatch f
       | _ -> NoMatch)
    | Wildcard -> FullMatch (f { Parts.prefix = List.rev seen; matched = s })
    | Match (x, fmt) ->
      (match s with
       | x' :: xs when x = x' -> match_target fmt f (x' :: seen) xs
       | _ -> NoMatch)
    | Conv ({ from_; _ }, fmt) ->
      (match s with
       | [] -> NoMatch
       | x :: xs ->
         (match from_ x with
          | None -> NoMatch
          | Some x' -> match_target fmt (f x') (x :: seen) xs))
  in
  match_target path handler [] params
;;

let router_of_route ((Route (path, _, _)) as route) =
  TrieRouter (PatternTrie.add (route_pattern path) route PatternTrie.empty)
;;

let union_parts = function
  | UnionRouter routers -> routers
  | router -> [ router ]
;;

let union first second =
  match first, second with
  | (TrieRouter first as left), (TrieRouter second as right) ->
    (try TrieRouter (PatternTrie.union first second) with
     | PatternTrie.IncompatibleWildcard -> UnionRouter [ left; right ])
  | _ -> UnionRouter (union_parts first @ union_parts second)
;;

let one_of routes =
  let rec add_routes trie = function
    | [] -> TrieRouter trie
    | (Route (path, _, _) as route) :: rest ->
      (try add_routes (PatternTrie.add (route_pattern path) route trie) rest with
       | PatternTrie.IncompatibleWildcard ->
         UnionRouter
           (List.map router_of_route (List.rev rest)
            @ [ router_of_route route; TrieRouter trie ]))
  in
  add_routes PatternTrie.empty (List.rev routes)
;;

let add_route ((Route (path, _, _)) as route) router =
  let patterns = route_pattern path in
  match router with
  | TrieRouter trie ->
    (try TrieRouter (PatternTrie.add patterns route trie) with
     | PatternTrie.IncompatibleWildcard -> UnionRouter [ router_of_route route; router ])
  | UnionRouter routers -> UnionRouter (router_of_route route :: routers)
;;

let map f (Route (r, h, g)) = Route (r, h, fun x -> f (g x))

let rec match_routes target = function
  | [] -> NoMatch
  | Route (r, h, f) :: rs ->
    (match parse_route r h target with
     | NoMatch -> match_routes target rs
     | FullMatch r -> FullMatch (f r)
     | MatchWithTrailingSlash r -> MatchWithTrailingSlash (f r))
;;

let rec match_in_router target = function
  | TrieRouter router -> match_routes target (PatternTrie.feed_params router target)
  | UnionRouter routers ->
    let rec first_match = function
      | [] -> NoMatch
      | router :: rest ->
        (match match_in_router target router with
         | NoMatch -> first_match rest
         | result -> result)
    in
    first_match routers
;;

let match' router ~target = match_in_router (Util.split_path target) router ;;

let ( /~ ) m path = m path
