Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
(* Require Import Coq.Lists.ListSet. *)
Import ListNotations.


(* simple types in Bell (p. 69)*)
Inductive type : Set :=
| Omega : type
| Unit : type
| Prod : type -> type -> type
| Power : type -> type.


(* a context is a set of variables and a type assignment to each variable *)
(* Note: These are variable contexts, as opposed to proposition contexts of Bell, which are defined later as environments *)
(* Given a context ctx = (X,f),
   (projT1 ctx) = X and (projT2 ctx) = f *)
(* We sometime write for clarity |Γ| and Γᵢ, respectively *)
Definition Ctx := { X : Type & X -> type }.



Definition Empty : Ctx := existT (fun x => x -> type) False (False_rec type).

(* Extend a context by one type: [Γ,a] *)
Definition Ext (ctx : Ctx) (a  : type) : Ctx :=
  existT (fun x => x -> type)
         (option (projT1 ctx))
         (fun x => match x with
                   | None => a
                   | Some i => (projT2 ctx i)
                   end).

(* Extend a context by a list of types:
   [Γ,a,b,...] for a list a::b::(...) *)
Fixpoint ExtLst (ctx : Ctx) (L : list type) : Ctx :=
  match L with
  | nil => ctx
  | a::L' => (ExtLst (Ext ctx a) L')
  end.

(* (Tm Γ a) is the set of terms of type a in context Γ *)
(* Note that variables are represented in deBruijn notation, that is
                             (corresponds to)
   (var [Γ,a] None)                 ~~~>  Γ,x:a ⊢ x:a
   (var [Γ,a,b] (Some None))        ~~~>  Γ,x:a,y:b ⊢ x:a
  and generally
   (var [Γ,aₙ,...,a₀] (Someⁱ None)) ~~~> Γ,xₙ:aₙ,...,x₀:a₀ ⊢ xᵢ : aᵢ
*)
Inductive Tm (ctx : Ctx) : type -> Type :=
| var : forall (i : projT1 ctx), Tm ctx (projT2 ctx i)
| star : Tm ctx Unit
| compr : forall a, Tm (Ext ctx a) Omega -> Tm ctx (Power a)
| pair : forall {a b}, Tm ctx a -> Tm ctx b -> Tm ctx (Prod a b)
| proj1 : forall {a b}, Tm ctx (Prod a b) -> Tm ctx a
| proj2 : forall {a b}, Tm ctx (Prod a b) -> Tm ctx b
| Eq : forall {a}, Tm ctx a -> Tm ctx a -> Tm ctx Omega
| In : forall {a}, Tm ctx a -> Tm ctx (Power a) -> Tm ctx Omega.

(* Context weakening, that is given
    Γ,Δ ⊢ s : b
   construct the term s' with
    Γ,a,Δ ⊢ s' : b  *)
(* The following context weakenings are assumed, but they should
   be derivable as recursive definitions... *)
(* We only treat the following special cases:
   Γ ⊢ s : a  —>  Γ,b ⊢ s' : a  *)
Parameter weaken0 : forall {ctx : Ctx} {a b} (s : Tm ctx a),
    (Tm (Ext ctx b) a).

(* Γ,a ⊢ s : c  —>  Γ,b,a ⊢ s' : c  *)
Parameter weaken1 : forall {ctx} { a b c },
    (Tm (Ext ctx a) c) -> (Tm (Ext (Ext ctx b) a) c).

(* Dependent context weakening, that is given
        i : |Γ|  and  s : (Tm Δ Γᵢ),
   return
         s' : (Tm [Δ,a] [Γ,a]_{i+1})    *)
Parameter weaken_dep : forall {ctx ctx' : Ctx} {a}
                          (i : projT1 ctx) (s : Tm ctx' (projT2 ctx i)),
    (Tm (Ext ctx' a) (projT2 (Ext ctx a) (Some i))).

Definition weaken0_lst {ctx a b} (ls : list (Tm ctx a)) :
    list (Tm (Ext ctx b) a) :=
  map weaken0 ls.

(* Given a valuation
     σ : (i : |Γ|) —> (Tm Δ Γᵢ)
   weaken the valuation to
     σ' : (i : |[Γ,τ]|) —> (Tm [Δ,τ] [Γ,τ]ᵢ)   *)
Fixpoint weaken_val {ctx ctx' : Ctx}{a}
         (sigma : forall (i : projT1 ctx), Tm ctx' (projT2 ctx i))
         (i : (option (projT1 ctx)))
  : Tm (Ext ctx' a) (projT2 (Ext ctx a) i) :=
  match i with
  | Some i' => (weaken_dep i' (sigma i'))
  | None => var (Ext ctx' a) None
  end.



(* Tm is not quite a monad on Γ, but almost, so given
     σ : (i : |Γ|) —> (Tm Δ Γᵢ),
   and
     s : (Tm Γ a)
   we define
     σ^*(s) : (Tm Δ a)
   which gives the substitution
     s[σ₀/x₀, ... , σₙ/xₙ]      *)
Fixpoint Tm_bind {ctx ctx' : Ctx} {a : type}
         (sigma : forall (i : projT1 ctx), Tm ctx' (projT2 ctx i))
         (s : Tm ctx a) : (Tm ctx' a) :=
  match s with
  | var i => (sigma i)
  | star => (star _)
  | compr a phi =>
    (compr _ a (@Tm_bind (Ext ctx a) (Ext ctx' a) _ (weaken_val sigma) phi))
  | pair _ _ s t => (pair _ (Tm_bind sigma s) (Tm_bind sigma t))
  | proj1 _ _ c => (proj1 _ (Tm_bind sigma c))
  | proj2 _ _ c => (proj2 _ (Tm_bind sigma c))
  | Eq _ s t => (Eq _ (Tm_bind sigma s) (Tm_bind sigma t))
  | In _ s t => (In _ (Tm_bind sigma s) (Tm_bind sigma t))
  end.

(* Given
   Γ,a ⊢ s : b  ,  Γ ⊢ u : a
   this gives the substitution
   —>   Γ ⊢ s[u/x₀] : b          *)
Definition subst0 {ctx : Ctx} {a b}
           (s : Tm (Ext ctx a) b) (u : Tm ctx a) : Tm ctx b :=
  Tm_bind (fun (i : (projT1 (Ext ctx a))) =>
             match i with
             | None => u
             | Some i' => var ctx i'
             end)
          s.

Definition subst0_lst {ctx : Ctx} {a b}
           (ls : list (Tm (Ext ctx a) b)) (u : Tm ctx a) : list (Tm ctx b) :=
  map (fun s => (subst0 s u)) ls.

(* Logical definitions from Bell (p. 70) *)
Definition Equiv {ctx : Ctx} (p q : Tm ctx Omega) : Tm ctx Omega :=
  (Eq _ p q).

Definition true {ctx : Ctx} : Tm ctx Omega :=
  (Eq _ (star _) (star _)).

Definition And {ctx : Ctx} (p q : Tm ctx Omega) : Tm ctx Omega :=
  (Eq _ (pair _ p q) (pair _ true true)).

Definition Imp {ctx : Ctx} (p q : Tm ctx Omega) : Tm ctx Omega :=
  (Equiv (And p q) p).

Definition Forall {ctx : Ctx} (a : type) (p : Tm (Ext ctx a) Omega)
  : Tm ctx Omega :=
  (Eq _ (compr _ a p) (compr _ a true)).

Definition false {ctx : Ctx} : Tm ctx Omega :=
  (Forall Omega (var (Ext ctx Omega) None)).

Definition Neg {ctx : Ctx} (p : Tm ctx Omega) : Tm ctx Omega :=
  (Imp p false).

Definition Or {ctx : Ctx} (p q : Tm ctx Omega) : Tm ctx Omega :=
  (Forall Omega (Imp (And (Imp (weaken0 p) (var (Ext ctx Omega) None))
                          (Imp (weaken0 q) (var (Ext ctx Omega) None)))
                     (var (Ext ctx Omega) None))).

Definition Exists {ctx : Ctx} (a : type) (p : Tm (Ext ctx a) Omega)
  : Tm ctx Omega :=
  (Forall Omega (Imp (Forall a (Imp (weaken1 p)
                                    (var (Ext (Ext ctx Omega) a) (Some None))))
                     (var (Ext ctx Omega) None))).


(* Context of propositions, which are what Bell calls contexts.
   To avoid ambiguity we call them environments. *)
Definition Env (ctx : Ctx) := list (Tm ctx Omega).

(* A sequent (p. 71) has the form
    Γ | φ₁, ..., φₙ ⊢ φ₀
   where for each i we have
    Γ ⊢ φᵢ : Ω,
   In particular this takes care of variables, so that
   the free variables in φᵢ are in Γ.        *)
Inductive Seq : forall (ctx : Ctx), (Env ctx) -> (Tm ctx Omega) -> Prop :=
| tautology {ctx p} :
    (Seq ctx [p] p)
| unity {ctx} :
    Seq (Ext ctx Unit) [] (Eq _ (var (Ext ctx Unit) None) (star _))
| equality {ctx a} {p : Tm (ExtLst ctx [a;a;a]) Omega}:
    Seq (ExtLst ctx [a;a])
        [(Eq (ExtLst ctx [a;a])
             (var (ExtLst ctx [a;a]) (Some None))
             (var (ExtLst ctx [a;a]) None));
         (subst0 p (var (ExtLst ctx [a;a]) (Some None)))]
        (subst0 p (var (ExtLst ctx [a;a]) None))
| product_beta {ctx a b} :
    Seq (ExtLst ctx [a;b]) []
        (Eq _ (proj1 _ (pair _ (var (ExtLst ctx [a;b]) (Some None))
                             (var (ExtLst ctx [a;b]) None)))
            (var (ExtLst ctx [a;b]) (Some None)))
| comprehension {ctx a} {p : Tm (Ext ctx a) Omega} :
    Seq (Ext ctx a) []
        (Equiv (In _ (var (Ext ctx a) None)
                   (weaken0 (compr _ a p))) p)
| thinning {ctx env p q} :
    (Seq ctx env p) -> (Seq ctx (q::env) p)
| cut {ctx env p q} :
    (Seq ctx env q) -> (Seq ctx (q::env) p) -> (Seq ctx env p)
| substitution {ctx a t} {env : Env (Ext ctx a)} {p : Tm _ Omega} :
    (Seq (Ext ctx a) env p) ->
    (Seq ctx (subst0_lst env t)
         (subst0 p t))
| extensionality {ctx env a} {s t : Tm ctx (Power a)} :
    (Seq (Ext ctx a) (weaken0_lst env)
         (Equiv (In _ (var (Ext ctx a) None) (weaken0 s))
                (In _ (var (Ext ctx a) None) (weaken0 t)))) ->
    (Seq (Ext ctx a) (weaken0_lst env)
         (Eq _ (weaken0 s) (weaken0 t)))
| equivalence {ctx env p q} :
    (Seq ctx (p::env) q) -> (Seq ctx (q::env) p) ->
    (Seq ctx env (Equiv p q)).
