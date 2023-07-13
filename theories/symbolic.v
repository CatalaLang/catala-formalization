From Coq Require Import List String ZArith.
From Autosubst Require Import Autosubst.
From Catala Require Import syntax continuations.
Import ListNotations.

(** Symbolic expressions *)
Inductive sym_expr :=
    | Sbool (b: bool)
    | Sint (i: Z)
    | Svar (s : string)
    | Sadd (e1 e2 : sym_expr)
    | Sclo (t: term) (sigma: var -> sym_expr)
    | Sempty
    | Sconflict.

Fixpoint eval_sym_expr (e : sym_expr) (env : string -> value) : result :=
    match e with
    | Sbool b => RValue (Bool b)
    | Sint i => RValue (Int i)
    | Svar s => RValue (env s)
    | Sadd e1 e2 =>
        match eval_sym_expr e1 env, eval_sym_expr e2 env with
        | RValue (Int i1), RValue (Int i2) =>RValue (Int (i1 + i2)%Z)
        | _, _ => RConflict
        end
    | _ => RConflict
    end.

(** Symbolic continuations *)
Inductive sym_cont :=
    | SCAppL (t1 : term) (* [ t1 \square ] *)
    | SCAppR (t2 : term) (* [ \square t2 ] *)
    | SCClosure (t_cl: {bind term}) (sigma_cl: var -> sym_expr)
    | SCDefault (o : option sym_expr) (ts: list term) (tj: term) (tc: term)
    | SCDefaultBase (tc: term)
    .

(** Symbolic constraints *)
Inductive sym_constraint :=
    | Eq (e1 e2 : sym_expr)
    | And (c1 c2 : sym_constraint)
    | Or (c1 c2 : sym_constraint)
    | Not (c : sym_constraint)
    .

(** Symbolic paths *)
Definition sym_path := list sym_constraint.

(** Symbolic stores *)
Definition sym_store := var -> sym_expr.

(** Symbolic states *)
Inductive sym_state :=
    (* Symbolic evaluation mode *)
    | sym_mode_eval (e : term) (stack : list sym_cont) (path : sym_path) (env : sym_store)
    (* Symbolic continuation mode *)
    | sym_mode_cont (stack : list sym_cont) (path : sym_path) (env : sym_store) (v : sym_expr).


Inductive sym_cred: sym_state -> sym_state -> Prop :=
    | sym_cred_var:
        forall x kappa phi sigma,
        sym_cred
            (sym_mode_eval (Var x) kappa phi sigma)
            (sym_mode_cont kappa phi sigma (sigma x))

    | sym_cred_app:
        forall t1 t2 kappa phi sigma,
        sym_cred
            (sym_mode_eval (App t1 t2) kappa phi sigma)
            (sym_mode_eval t1 ((SCAppR t2) :: kappa) phi sigma)
    
    | sym_cred_clo:
        forall t kappa phi sigma,
        sym_cred
            (sym_mode_eval (Lam t) kappa phi sigma)
            (sym_mode_cont kappa phi sigma ((Sclo t sigma))).

(* 
    | cred_arg:
        (* $\lcont (\square\ e_2) \cons \kappa, \sigma, Clo (x, t_{cl}, \sigma_{cl}) \rcont \leadsto \leval e_2, (Clo(x, t_{cl}, \sigma_{cl})\ \square) \cons \kappa, \sigma \reval$ *)
        forall t2 kappa sigma tcl sigmacl,
        cred
            (mode_cont ((CAppR t2)::kappa) sigma (RValue (Closure tcl sigmacl)))
            (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)

    | cred_beta:
        (* $\lcont(Clo(x, t_{cl}, \sigma_{cl})\ \square) \cons \kappa, \sigma, v \rcont \leadsto \leval t_{cl}, \kappa, (x\mapsto v) \cons\sigma_{cl} \reval$ *)
        forall tcl sigmacl kappa sigma v, 
        cred
            (mode_cont ((CClosure tcl sigmacl)::kappa) sigma (RValue v))
            (mode_eval tcl kappa  (v .: sigmacl))


    | cred_default:
        (* $\leval \synlangle es \synmid e_j \synjust e_c \synrangle, \kappa, \sigma \reval \leadsto \lcont (\mathtt{Def}(\synnone, es, e_j, e_c)) \cons \kappa, \sigma, \synempty \rcont$ *)
        
        forall ts tj tc kappa sigma,
        cred
            (mode_eval (Default ts tj tc) kappa sigma)
            (mode_cont ((CDefault None ts tj tc)::kappa) sigma REmpty)

    | cred_defaultunpack:
        (* $\lcont \mathtt{Def}(o, e_h \cons es, e_j, e_c) \cons \kappa, \sigma, \synempty \rcont \leadsto \leval e_h, \mathtt{Def}(o, es, e_j, e_c) \cons \kappa, \sigma \reval$ *)
        forall o th ts tj tc kappa sigma,
        cred
            (mode_cont ((CDefault o (th::ts) tj tc)::kappa) sigma REmpty)
            (mode_eval th ((CDefault o ts tj tc)::kappa) sigma)

    | cred_defaultnone:
        (* $\lcont \mathtt{Def}(\synnone, e_h \cons es, e_j, e_c) \cons \kappa, \sigma, v \rcont \leadsto \leval e_h, \mathtt{Def}(\synsome(v), es, e_j, e_c) \cons \kappa, \sigma \reval$ *)
        forall ts tj tc kappa sigma v,
        cred
            (mode_cont ((CDefault None ts tj tc)::kappa) sigma (RValue v))
            (mode_cont ((CDefault (Some v) ts tj tc)::kappa) sigma REmpty)

    | cred_defaultconflict:
        (* $\lcont \mathtt{Def}(\synsome(v), es, e_j, e_c) \cons \kappa, \sigma, v' \rcont \leadsto \lcont \mathtt{Def}(\synsome(v), es, e_j, e_c)  \cons \kappa, \sigma, \synconflict \rcont$ *)
        forall ts tj tc kappa sigma v v',
        cred
            (mode_cont ((CDefault (Some v) ts tj tc)::kappa) sigma (RValue v'))
            (mode_cont kappa sigma RConflict)

    | cred_defaultvalue:
        (* $\lcont \mathtt{Def}(\synsome(v), [], e_j, e_c) \cons \kappa, \sigma, \synempty \rcont \leadsto \lcont \kappa, \sigma, v \rcont$ *)
        forall v tj tc kappa sigma,
        cred 
            (mode_cont ((CDefault (Some v) [] tj tc)::kappa) sigma REmpty)
            (mode_cont kappa sigma (RValue v))

    (* | cred_defaultnonefinal: (* not needed *)
        (* $\lcont \mathtt{Def}(\synnone, [], e_j, e_c) \cons \kappa, \sigma, v \rcont \leadsto \lcont \kappa, \sigma, v \rcont$ \hfill $v \neq \synempty, \synconflict$ *)
        todo *)

    | cred_defaultbase:
        (* $\lcont \mathtt{Def}(\synnone, [], e_j, e_c) \cons \kappa, \sigma, \synempty \rcont \leadsto \leval e_j, \synlanglemid \square \synjust e_c \synrangle \cons \kappa, \sigma \reval$ *)
        forall tj tc kappa sigma,
        cred 
            (mode_cont ((CDefault None [] tj tc)::kappa) sigma REmpty)
            (mode_eval tj ((CDefaultBase tc)::kappa) sigma)

    | cred_defaultbasetrue:
        (* $\lcont \synlanglemid \square \synjust e_c \synrangle \cons \kappa, \sigma, \syntrue \rcont \leadsto \leval e_c, \kappa, \sigma \reval$ *)
        forall tc kappa sigma,
        cred
            (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool true)))
            (mode_eval tc kappa sigma)

    | cred_defaultbasefalse:
        (* $\lcont \synlanglemid \square \synjust e_c \synrangle \cons \kappa, \sigma, \synfalse \rcont \leadsto \lcont \kappa, \sigma, \synempty \rcont$ *)
        forall tc kappa sigma,
        cred
            (mode_cont ((CDefaultBase tc)::kappa) sigma (RValue (Bool false)))
            (mode_cont kappa sigma REmpty)

    | cred_empty:
        (* $\lcont \phi \cons \kappa, \sigma, \synempty \rcont \leadsto \lcont \kappa, \sigma, \synempty \rcont$ \hfill $\forall o\ es\ e_j\ e_c,\ \phi \neq \mathtt{Def}(o, es, e_j, ec)$ *)
        forall phi kappa sigma,
        (forall o ts tj tc, phi <> CDefault o ts tj tc) ->
        cred
            (mode_cont (phi::kappa) sigma REmpty)
            (mode_cont kappa sigma REmpty)

    | cred_conflict:
        (* $\lcont \phi \cons \kappa, \sigma, \synconflict \rcont \leadsto \lcont \kappa, \sigma, \synconflict \rcont$ *)
        forall phi kappa sigma,
        cred
            (mode_cont (phi::kappa) sigma RConflict)
            (mode_cont kappa sigma RConflict)
    | cred_confict_intro:
        forall kappa sigma,
        cred
            (mode_eval Conflict kappa sigma)
            (mode_cont kappa sigma RConflict)
    | cred_empty_intro:
        forall kappa sigma,
        cred
            (mode_eval Empty kappa sigma)
            (mode_cont kappa sigma REmpty)
. *)