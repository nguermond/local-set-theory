
exception Implementation of string
exception Typing of string


open Utilities
open Format




module Prolog =
  struct
    open Elpi
    open Elpi.API

    type theory = Setup.elpi * Compile.program

    let get_elpi (thy : theory) : Setup.elpi =
      (let (elpi,_) = thy in elpi)

    let get_program (thy : theory) : Compile.program =
      (let (_,prog) = thy in prog)

    let init () : theory =
      (printf "Initializing Elpi...@\n");
      (let (elpi,_) = (Setup.init
                      ~builtins:[Builtin.std_builtins]
                      ~basedir:"/home/nathan/Projects/local-set-theory/"
                      []) in
       (let prog = (Parse.program
                      ~elpi:elpi
                      ~print_accumulated_files:true
                      ["dependent-type-theory-backchain-types.elpi"]) in
        (elpi,(Compile.program
                 ~flags:Compile.default_flags
                 ~elpi:elpi
                 [prog]))))

    let prove (thy : theory) (str_query : string) : bool =
      (printf "Proving: %s" str_query);
      (print_endline "");
      (let query = (Parse.goal (Ast.Loc.initial "") str_query) in
       (let query = (Compile.query (get_program thy) query) in
        (let exec = (Compile.optimize query) in
         (let outcome = (Execute.once exec) in
          (match outcome with
           | Success _ -> (printf "Success!@\n"); true
           | Failure -> (printf "Failure!@\n"); false
           | NoMoreSteps -> (printf "No more steps!@\n"); false)))))

    (* Compile.extend seems not be available in current release of Elpi! *)
    (* let store_lemma (thy : theory) (str_clause : string) : theory =
     *   (let elpi = (get_elpi thy) in
     *    (let clause = (Parse.program_from_stream
     *                     ~elpi:elpi
     *                     (Ast.Loc.initial "")
     *                     (Stream.of_string str_clause)) in
     *     (let unit = (Compile.unit
     *                    ~elpi:elpi
     *                    ~flags:Compile.default_flags
     *                    clause) in
     *      (let prog = (Compile.extend
     *                     ~base:(get_program thy)
     *                     [unit]) in
     *       (elpi,prog))))) *)


    (* Add definition/axiom *)

  end;;


module Term =
  struct
    open List

    type var = int
    type symbol = string

    type term = UVar of var
              | LVar of var
              | Var of var
              | Unit
              | Omega
              | Prod of term * term
              | Power of term
              | Pi of term * term
              | Sub of term * term
              | Star
              | Eq of term * term * term
              | In of term * term * term
              | Pair of term * term
              | Compr of term * term
              | Lam of term * term
              | App of term * term
              | Proj1 of term
              | Proj2 of term
              | Cons of symbol * (term list)

    type context = term list

    let rec pp_term ppf (tm : term) =
      (match tm with
       | UVar x -> (fprintf ppf "[%d]" x)
       | LVar x -> (fprintf ppf "(%d)" x)
       | Var x -> (fprintf ppf "%d" x)
       | Unit -> (fprintf ppf "U")
       | Omega -> (fprintf ppf "Ω")
       | Prod (a,b) -> (fprintf ppf "@[<1>%a × %a@]" pp_term a pp_term b)
       | Power a -> (fprintf ppf "P(%a)" pp_term a)
       | Pi (a,fam) -> (fprintf ppf "@[<1>Π(%a, %a)@]" pp_term a pp_term fam)
       | Sub (a,phi) -> (fprintf ppf "@[<1>(%a | %a)@]" pp_term a pp_term phi)
       | Star -> (fprintf ppf "⋆")
       | Eq (_,s,t) -> (fprintf ppf "@[<1>%a = %a@]" pp_term s pp_term t)
       | In (_,s,t) -> (fprintf ppf "@[<1>%a ∈ %a@]" pp_term s pp_term t)
       | Pair (s,t) -> (fprintf ppf "@[<1>(%a, %a)@]" pp_term s pp_term t)
       | Compr (a,phi) -> (fprintf ppf "@[<1>{%a | %a}@]" pp_term a pp_term phi)
       | Lam (a,s) -> (fprintf ppf "@[<1>(λ%a. %a)@]" pp_term a pp_term s)
       | App (s,t) -> (fprintf ppf "@[<1>(%a %a)@]" pp_term s pp_term t)
       | Proj1 u -> (fprintf ppf "π₁(%a)" pp_term u)
       | Proj2 u -> (fprintf ppf "π₂(%a)" pp_term u)
       | Cons(sym,args) -> (fprintf ppf "(%s@ %a)" sym pp_term_lst args))

    and pp_term_lst ppf (lst : term list) =
      (match lst with
       | [] -> (fprintf ppf "")
       | [tm] -> (fprintf ppf "%a" pp_term tm)
       | tm::lst' -> (fprintf ppf "%a,@ %a" pp_term tm pp_term_lst lst'))

    let pp_context ppf (ctx : context) =
      (fprintf ppf "@[<2>[%a]@]" pp_term_lst (rev ctx))


    let term_true : term =
      Cons("tt",[])

    let term_and (s : term) (t : term) : term =
      Cons("and",[s,t])


    let term_forall (a : term) (phi : term) : term =
      Cons("forall",[Lam(a,phi)])

    (* Flatten comprehension types. This should give
       an over approximation of the type.
       Note that we do not flatten the constraints on a
       domain of a Pi type. *)
    let rec flatten (ty : term) : term =
      (match ty with
       | UVar _ -> ty
       | Unit | Omega -> ty
       | Prod (a,b) -> Prod (flatten a, flatten b)
       | Power a -> Power (flatten a)
       | Pi (a,fam) -> Pi (a, flatten fam)
       | Sub (a,_) -> (flatten a)
       | _ -> (assert false))
  end;;

module Valuation =
  struct
    open Term
    open List

    type valuation = var -> term

    let singleton (var : var) (tm : term) : valuation =
      (fun x -> (if x = var then tm else (Var x)))

    let identity : valuation =
      (fun x -> (Var x))

    (* This mutual recursion is very questionable, but hey, it works *)
    let rec lift (sigma : var -> term) (tm : term) : term =
      (match tm with
       | UVar _ -> tm
       | LVar _ -> tm
       | Var x -> (sigma x)
       | Unit | Omega -> tm
       | Prod (a,b) -> Prod (lift sigma a, lift sigma b)
       | Power a -> Power (lift sigma a)
       | Pi (a,fam) -> Pi (lift sigma a, lift (bind_var sigma) fam)
       | Sub (a,phi) -> Sub (lift sigma a, lift (bind_var sigma) phi)
       | Star -> tm
       | Eq (a,s,t) -> Eq (lift sigma a, lift sigma s, lift sigma t)
       | In (a,s,t) -> In (lift sigma a, lift sigma s, lift sigma t)
       | Pair (s,t) -> Pair (lift sigma s, lift sigma t)
       | Compr (a,phi) -> Compr (lift sigma a, lift (bind_var sigma) phi)
       | Lam (a,s) -> Lam (lift sigma a, lift (bind_var sigma) s)
       | App (t,u) -> App (lift sigma t, lift sigma u)
       | Proj1 u -> Proj1 (lift sigma u)
       | Proj2 u -> Proj2 (lift sigma u))

    and bind_var (sigma : var -> term) (x : var) : term =
      (if x = 0 then (Var 0) else (shift (sigma (x - 1)) 1))

    and shift (tm : term) (i : int) : term =
      (let sigma = (fun x -> (Var (x + i))) in
       (lift sigma tm))

    let unbind_var (sigma : var -> term) (x : var) : term =
      (shift (sigma (x + 1)) (-1))

    (* This should always be applied as
     *   (shift (subst1 tm1 (shift tm2 1)) (-1))
     * since subst1 should pop the context,
     * unless we want to shift tm2 by more than 1 *)
    let subst1 (tm1 : term) (tm2 : term) : term =
      (let sigma = (fun x -> (if x = 0 then tm2 else (Var x))) in
       (lift sigma tm1))

    let substi (tm1 : term) (tm2 : term) (i : int) : term =
      (let sigma = (fun x -> (if x = i then tm2 else (Var x))) in
       (lift sigma tm1))

    (* let rec simultaneous_substitution (tms : term list) (tm : term) : term =
     *   (match tms with
     *    | [] -> tm
     *    | tm'::tms' -> (let tm = (shift (subst1 tm (shift tm' (length tms))) (-1)) in
     *                    (simultaneous_substitution tms' tm))) *)

    (* Checks whether ctx |- x : ty *)
    let defined_in_context (ctx : context) (i : var) (ty : term) : bool =
      ((i >= 0) && (i < (length ctx)) &&
         (nth ctx i = (shift ty (- (i + 1)))))

    let get_type_in_context (ctx : context) (i : var) : term =
      (assert (i >= 0 && i < (length ctx)));
      (shift (nth ctx i) (i + 1))
  end;;

module TermConversion =
  struct
    open Term
    open Valuation
    open List

    (* Convert term to Prolog string *)
    (* (UVar n) is converted to Xn -- for universal variables *)
    (* (LVar n) is converted to xn -- for bound variables *)
    (* Conversion needs to reduce β-redexes! *)
    (* λProlog will not do it for us! *)
    let rec convert_term_x (tm : term) (i : int) : string * (int list) =
      (let (res,uvars) =
         (match tm with
          | UVar i -> ("u"^(string_of_int i), [i])
          | LVar i -> ("x"^(string_of_int i), [])
          | Star -> ("star", [])
          | Eq (a,s,t) ->
             (let ((a,u0),(s,u1),(t,u2)) = (convert_term_x (Term.flatten a) i,
                                            convert_term_x s i,
                                            convert_term_x t i) in
              ("(eq "^a^" "^s^" "^t^")", append u0 (append u1 u2)))
          | In (a,s,t) ->
             (let ((a,u0),(s,u1),(t,u2)) = (convert_term_x (Term.flatten a) i,
                                            convert_term_x s i,
                                            convert_term_x t i) in
              ("(in "^a^" "^s^" "^t^")", append u0 (append u1 u2)))
          | Pair (s,t) ->
             (let ((s,u1),(t,u2)) = (convert_term_x s i,
                                     convert_term_x t i) in
              ("(pair "^s^" "^t^")", append u1 u2))
          | Compr (a,s) ->
             (let s = (shift (subst1 s (LVar i)) (-1)) in
              (let ((a,u0),(s,u1)) = (convert_term_x (Term.flatten a) i,
                                      convert_term_x s (i+1)) in
               ("(compr "^a^" x"^(string_of_int i)^"\\"^s^")", append u0 u1)))
          | Lam (a,s) ->
             (let s = (shift (subst1 s (LVar i)) (-1)) in
              (let ((a,u0),(s,u1)) = (convert_term_x (Term.flatten a) i,
                                      convert_term_x s (i+1)) in
               ("(lam "^a^" x"^(string_of_int i)^"\\"^s^")", append u0 u1)))
          | App (s,t) ->
             (let ((s,u1),(t,u2)) = (convert_term_x s i,
                                     convert_term_x t i) in
              ("("^s^" "^t^")", (append u1 u2)))
          | Proj1 p -> (let (p,u0) = (convert_term_x p i) in
                        ("(proj1 "^p^")", u0))
          | Proj2 p -> (let (p,u0) = (convert_term_x p i) in
                        ("(proj2 "^p^")", u0))
          | Unit -> ("unit", [])
          | Omega -> ("omega", [])
          | Prod(a,b) ->
             (let ((a,u0),(b,u1)) = (convert_term_x (Term.flatten a) i,
                                     convert_term_x (Term.flatten b) i) in
              ("(prod "^a^" "^b^")", append u0 u1))
          | Power a -> (let (a,u0) = (convert_term_x (Term.flatten a) i) in
                        ("(power "^a^")", u0))
          | Pi(a,fam) ->
             (let fam = (shift (subst1 fam (LVar i)) (-1)) in
              (let ((a,u0),(fam,u1)) = (convert_term_x a i,
                                        convert_term_x (Term.flatten fam) (i+1)) in
               ("(dprod "^a^" x"^(string_of_int i)^"\\"^fam^")", append u0 u1)))
          | Sub(a,phi) ->
             (let phi = (shift (subst1 phi (LVar i)) (-1)) in
              (let ((a,u0),(phi,u1)) = (convert_term_x a i,
                                        convert_term_x phi (i+1)) in
               ("(sub "^a^" x"^(string_of_int i)^"\\"^phi^")", append u0 u1)))
          | Var _ -> (assert false))
       in (* (printf "@[%a @ --> %s@\n@]" pp_term tm res); *)
          (res,uvars))

       let convert_term (tm : term) : string * (int list) =
         (convert_term_x tm 0)

  end;;


module Sequent =
  struct
    open Term
    open TermConversion
    open Valuation
    open List

    type sequent = (term list) * term

    let pp_sequent ppf (seq : sequent) =
      (let (hyps,conc) = seq in
       (fprintf ppf "@[<2>%a ⊢ @ %a@]" pp_term_lst hyps pp_term conc))

    let add_hyp (hyp : term) (seq : sequent) : sequent =
      (let (hyps,conc) = seq in
       (hyp::hyps,conc))

    let subst1_seq (seq : sequent) (tm : term) : sequent =
      (let (hyps,conc) = seq in
       ((map (fun x -> subst1 x tm) hyps),
        (subst1 conc tm)))

    let substi_seq (seq : sequent) (tm : term) (i : int) : sequent =
      (let (hyps,conc) = seq in
       ((map (fun x -> substi x tm i) hyps),
        (substi conc tm i)))

    let shift_seq (seq : sequent) (k : int) : sequent =
      (let (hyps,conc) = seq in
       ((map (fun x -> shift x k) hyps), shift conc k))

    let rec translate_context_x (ctx : context) (seq : sequent) (i : int) : sequent =
      (let result =
         (match ctx with
          | [] -> seq
          | a::ctx' ->
             (match a with
              | Unit -> (let seq = (shift_seq (subst1_seq seq Star) (-1)) in
                         (translate_context_x ctx' seq i))
              | Omega -> (let seq = (shift_seq (subst1_seq seq (UVar i)) (-1)) in
                          (translate_context_x ctx' seq (i+1)))
              | Prod (a,b) -> (let ctx' = ((shift b 1)::a::ctx') in
                               (let seq = (shift_seq seq 1) in
                                (let seq = (substi_seq seq (Pair (Var 1, Var 0)) 1) in
                                 (translate_context_x ctx' seq i))))
              | Power a -> (let seq = (subst1_seq seq (Compr (a, (UVar i)))) in
                            (let seq = (shift_seq seq (-1)) in
                             (translate_context_x ctx' seq (i+1))))
              | Pi _ -> (let seq = (shift_seq (subst1_seq seq (UVar i)) (-1)) in
                         (translate_context_x ctx' seq (i+1)))
              | Sub (a,phi) -> (let seq = (add_hyp phi seq) in
                                (translate_context_x (a::ctx') seq i))
              | _ -> (printf "Failure on %a@\n" pp_term a); (assert false)))
       in result)

    let translate_context (ctx : context) (seq : sequent) : sequent =
      (translate_context_x ctx seq 0)

    (* Convert sequent to prolog query *)
    (* It is assumed that seq comes from a translated context *)
    let convert_seq (seq : sequent) : string =
      (let (hyps,conc) = seq in
       let hyps = (map (fun x -> convert_term x) hyps) in
       let (conc,conc_uvars) = (convert_term conc) in
       let uvars = (fold_right (fun (_,u1) u2 ->
                        (append u1 u2)) hyps conc_uvars) in
       let uvars = (sort_uniq (-) uvars) in
       let uvars = (fold_right (fun i str -> "u"^(string_of_int i)^" "^str)
                      uvars "") in
       let hyps = (fold_right (fun (tm,_) str -> tm^","^str) hyps "") in
       let universals = (if uvars = "" then "("
                         else "(pi "^uvars^"\\ ") in
       let proof = "" in
       (universals^"(thm ["^hyps^"] "^conc^" ["^proof^"] _))"))

    let prove (prog : Prolog.theory) (ctx : context) (seq : sequent) : bool =
      (let seq = (translate_context ctx seq) in
       (let str = (convert_seq seq) in
        (Prolog.prove prog str)))
  end;;



module TypeCheck =
  struct
    open Term
    open Valuation
    open Sequent
    open List
    open Prolog

    (* Given a type, return its flattened overapproximation
       together with a propositional constraint, such that whenever
           (lift_constraints ty) = (ty', phi),
       then
           ty <: Sub(ty',phi)  and  Sub(ty',phi) <: ty      *)
    let rec lift_constraints (ty : term) : term * (term option) =
      (match ty with
       | Unit | Omega -> (ty, None)
       | Prod(a,b) ->
          (let ((a,mphi),(b,mpsi)) = (lift_constraints a, lift_constraints b) in
           (match (mphi,mpsi) with
            | (Some phi, Some psi) ->
               (Prod(a,b), Some (term_and (subst1 phi (Proj1 (Var 0)))
                                   (subst1 psi (Proj2 (Var 0)))))
            | (Some phi, None) -> (Prod(a,b), Some (subst1 phi (Proj1 (Var 0))))
            | (None, Some psi) -> (Prod(a,b), Some (subst1 psi (Proj2 (Var 0))))
            | (None, None) -> (Prod(a,b), None)))
       | Power a ->
          (let (a,mphi) = (lift_constraints a) in
           (match mphi with
            | Some phi ->
               (Power a, Some (Eq (Power a, Var 0, Compr(a, phi))))
            | None -> (Power a, None)))
       | Pi(a,fam) ->
          (let (fam,mphi) = (lift_constraints fam) in
           (match mphi with
            | Some phi ->
               (let phi = (shift (subst1 phi (App(Var 2,Var 1))) (-1)) in
                (Pi(a,fam), Some (term_forall a phi)))
            | None -> (Pi(a,fam), None)))
       | Sub(a, phi) ->
          (let (a,mpsi) = (lift_constraints a) in
           (match mpsi with
            | Some psi -> (a, Some (term_and phi psi))
            | None -> (a, Some phi)))
       | _ -> (assert false))


    (* infers the flattened type of tm *)
    let rec infer_type (ctx : context) (tm : term) : term =
      (match tm with
       | Var i -> (Term.flatten (get_type_in_context ctx i))
       | Star -> Unit
       | Eq(_,_,_) -> Omega
       | In(_,_,_) -> Omega
       | Pair(s,t) -> Prod(infer_type ctx s, infer_type ctx t)
       | Compr(a,_) -> Power(Term.flatten a)
       | Lam(a,s) -> Pi(a, infer_type (a::ctx) s)
       | Proj1 u -> (match (infer_type ctx u) with
                     | Prod (a,_) -> a
                     | _ -> (assert false))
       | Proj2 u -> (match (infer_type ctx u) with
                     | Prod (_,b) -> b
                     | _ -> (assert false))
       | _ -> (assert false))

    (* ty is assumed to be a flat type *)
    let rec wf_term_flat (prog : theory) (ctx : context)
              (tm : term) (ty : term) : bool =
      (assert (Term.flatten ty = ty));
      (match (tm,ty) with
       | (_ , Sub(_,_)) -> (assert false)
       | (Var i, _) -> (Term.flatten (get_type_in_context ctx i) = ty)
       | (Star, Unit) -> true
       | (Eq(a,s,t), Omega) -> (wf_term prog ctx s a) &&
                                 (wf_term prog ctx t a)
       | (In(a,s,t), Omega) -> (wf_term prog ctx s a) &&
                                 (wf_term prog ctx t (Power a))
       | (Pair(s,t), Prod(a,b)) -> (wf_term_flat prog ctx s a) &&
                                     (wf_term_flat prog ctx t b)
       | (_, Prod(a,b)) -> (wf_term_flat prog ctx (Proj1 tm) a) &&
                             (wf_term_flat prog ctx (Proj2 tm) b)
       | (Compr(a,phi), Power b) -> (wf_term_flat prog (a::ctx) phi Omega) &&
                                      (subtype prog ctx a b)
       | (Lam(a,s), Pi(b,fam)) -> (subtype prog ctx b a) &&
                                    (wf_term_flat prog (a::ctx) s fam)
       | (Proj1 Pair(s,_), a) -> (wf_term_flat prog ctx s a)
       | (Proj2 Pair(_,t), b) -> (wf_term_flat prog ctx t b)
       | (Proj1 u, a) -> (match (infer_type ctx u) with
                          | Prod(a',_) -> (a = a')
                          | _ -> (assert false))
       | (Proj2 u, b) -> (match (infer_type ctx u) with
                          | Prod(_,b') -> (b = b')
                          | _ -> (assert false))
       | (App(t,u), b) -> (let a = (infer_type ctx u) in
                           (match (infer_type ctx t) with
                            | Pi(a', fam) -> (subtype prog ctx a a') &&
                                               (subst1 fam u = b)
                            | _ -> (assert false)))
       | _ -> (assert false))

    and subtype (prog : theory) (ctx : context) (a : term) (b : term) : bool =
      (wf_term prog (a::ctx) (Var 0) b)

    and wf_term (prog : theory) (ctx : context) (tm : term) (ty : term) : bool =
      (let result =
         (let (flat_ty,mphi) = (lift_constraints ty) in
          match mphi with
          | None -> (assert (flat_ty = ty)); (wf_term_flat prog ctx tm ty)
          | Some phi ->
             (wf_term_flat prog ctx tm flat_ty) &&
               (let seq = ([], In(flat_ty,tm,Compr(flat_ty,phi))) in
                (Sequent.prove prog ctx seq)))
       in (fail_printf result "@[<2>Checking %a ⊢ %a : %a@\n@]"
             pp_context ctx pp_term tm pp_term ty); result)

    let rec wf_type (prog : theory) (ctx : context) (ty : term) : bool =
      (let result =
         (match ty with
          | Unit | Omega -> true
          | Prod (a,b) -> ((wf_type prog ctx a) && (wf_type prog ctx b))
          | Power a -> (wf_type prog ctx a)
          | Pi (a,fam) -> ((wf_type prog ctx a) && (wf_type prog (a::ctx) fam))
          | Sub (a,phi) -> ((wf_type prog ctx a) &&
                              (wf_term prog (a::ctx) phi Omega))
          | _ -> false)
       in (fail_printf result "@[<2>Checking %a ⊢ %a@\n@]"
             pp_context ctx pp_term ty); result)

    let rec wf_context (prog : theory) (ctx : context) : bool =
      (match ctx with
       | [] -> true
       | ty::ctx' -> ((wf_context prog ctx') && (wf_type prog ctx' ty)))


    let rec wf_sequent (prog : theory) (ctx : context) (seq : sequent) =
      (let (hyps,conc) = seq in
       (match hyps with
        | [] -> (wf_term prog ctx conc Omega)
        | p::hyps' -> (wf_term prog ctx p Omega) &&
                        (wf_sequent prog ctx (hyps',conc))))
  end;;



module Tests =
  struct
    open List
    open Term
    open TypeCheck
    open Sequent

    let tests =  [([Sub(Unit,Eq(Unit,Var 0,Star))],([], Eq(Unit,Var 0,Star)));
                  ([], ([],In(Unit,Star,Compr(Unit,Eq(Unit,Var 0,Star)))));
                  ([Sub(Unit,Eq(Unit,Var 0,Star))],
                   ([], Eq(Sub(Unit,Eq(Unit, Var 0, Star)),Var 0,Var 0)));
                  ([Sub(Prod(Unit,Unit),Eq(Unit,Proj1 (Var 0), Proj2 (Var 0)))],
                   ([], Eq(Unit, Proj2 (Var 0), Proj1 (Var 0))));
                  ([],([], Eq (Pi (Unit,Sub(Unit,Eq(Unit,Var 0,Var 1))),
                               Lam (Unit, Var 0),
                               Lam (Unit, Var 0))));
                  ([Sub(Omega,Eq(Omega,Var 0, Var 1));
                    Sub(Omega,Eq(Omega,Var 0, Var 1)); Omega],
                   ([], Eq(Omega, Var 0, Var 2)))
                 ]

    let main = (let prog = Prolog.init() in
                (for i=0 to ((length tests) - 1) do
                   (let (ctx,seq) = (nth tests i) in
                    (printf "Test %i:@\n %a | %a@\n" i
                       pp_context ctx pp_sequent seq);
                    (let wfctx = (wf_context prog ctx) in
                     (let wfseq = (wfctx && (wf_sequent prog ctx seq)) in
                      (let wfthm = (wfseq && (Sequent.prove prog ctx seq)) in
                       (assert wfthm);
                       (printf "Ok@\n")))))
                 done;))
  end;;


Tests.main;;
