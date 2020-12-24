
module Format =
  struct
    include Format

    let fail_printf (b : bool) : 'a -> 'b =
      (if b then (ifprintf std_formatter)
       else (printf))

  end;;



exception OutOfBounds of string


module List =
  struct
    include List
    open Format

    let rec iter0 (f : 'a -> unit) (f0 : 'a -> unit) (ls : 'a list) =
      (match ls with
       | [] -> ()
       | [x] -> f0 x
       | x::ls' -> (f x); (iter0 f f0 ls'))

    let index (x : 'a) (ls : 'a list) : int =
      (let rec index (ls : 'a list) (i : int) =
         (match ls with
          | [] -> (raise (OutOfBounds "Index out of bounds!"))
          | a::ls -> (if (a = x) then i else (index ls (i+1))))
       in (index ls 0))

    let index_opt (x : 'a) (ls : 'a list) : int option =
      (let rec index_opt (ls : 'a list) (i : int) =
         (match ls with
          | [] -> None
          | a::ls -> (if (a = x) then (Some i) else (index_opt ls (i+1))))
       in (index_opt ls 0))

    let find_opti (p : 'a -> bool) (lst : 'a list) : int option =
      (let rec find_opti (lst : 'a list) (i : int) =
         (match lst with
          | [] -> None
          | x::ls -> (if (p x) then Some i else (find_opti ls (i+1))))
       in (find_opti lst 0))

    let rec nth_tl (xs : 'a list) (i : int) : 'a list =
      (if i = 0 then xs
       else (nth_tl (tl xs) (i - 1)))

    let pp_string_list ppf (ls : string list) =
      (iter0 (fprintf ppf "%s ") (fprintf ppf "%s") ls)

    let pp_int_list ppf (ls : int list) =
      (iter0 (fprintf ppf "%i ") (fprintf ppf "%i") ls)

    let range i k : int list =
      (init k (fun x -> x + i))
  end;;
