Require Import syntax.

Import List.ListNotations.
Open Scope list_scope.

Inductive result :=
    | RValue (v: value)
    | REmpty
    | RConflict
.

Inductive cont :=
    | CAppL (t1: term) (* [t1 \square] *)
    | CAppR (t2: term) (* [\square t2] *)
    | CClosure (t_cl: {bind term}) (sigma_cl: var -> value)
        (* [Clo(x, t_cl, sigma_cl) \sigma] Since we are using De Bruijn indices, there is no variable x. *)
    | CDefault (o: option value) (ts: list term) (tj: term) (tc: term)
        (* [Def(o, ts, tj, tc)] *)
    | CDefaultBase (tc: term)
        (* [ <| \square :- tc >] *)
.

Inductive state :=
    | mode_eval (e: term) (stack: list cont) (env: var -> value)
    | mode_cont (stack: list cont) (env: var -> value) (result: result)
.

Inductive cred: state -> state -> Prop :=
    | cred_var:
        (* $\leval \synvar x, \kappa, \sigma \reval \leadsto \lcont\kappa, \sigma, \sigma(x) \rcont$ *)

        forall x kappa sigma v,
        cred (mode_eval (Var x) kappa sigma) (mode_cont kappa sigma (RValue v))

    | cred_app:
        (* $\leval e_1\ e_2, \kappa, \sigma \reval \leadsto \leval e_1, (\square\ e_2) \cons \kappa, \sigma \reval $ *)
        forall t1 t2 kappa sigma,
        cred (mode_eval (App t1 t2) kappa sigma) (mode_eval t1 ((CAppR t2) :: kappa) sigma)
    
    | cred_clo:
        (* $\leval \lambda x. t, \kappa, \sigma \reval \leadsto \lcont\kappa, \sigma, Clo (x, t, \sigma) \rcont$ *)
        forall t kappa sigma,
        cred (mode_eval (Lam t) kappa sigma) (mode_cont kappa sigma (RValue (Closure t sigma)))


    
    | cred_arg:
        (* $\lcont (\square\ e_2) \cons \kappa, \sigma, Clo (x, t_{cl}, \sigma_{cl}) \rcont \leadsto \leval e_2, (Clo(x, t_{cl}, \sigma_{cl})\ \square) \cons \kappa, \sigma \reval$ *)

        forall t2 kappa sigma tcl sigmacl,
        cred (mode_cont ((CAppR t2)::kappa) sigma (RValue (Closure tcl sigmacl))) (mode_eval t2 ((CClosure tcl sigmacl)::kappa) sigma)

    | cred_beta:
        (* $\lcont(Clo(x, t_{cl}, \sigma_{cl})\ \square) \cons \kappa, \sigma, v \rcont \leadsto \leval t_{cl}, \kappa, (x\mapsto v) \cons\sigma_{cl} \reval$ *)
        forall tcl sigmacl kappa sigma v, 
        cred (mode_cont ((CClosure tcl sigmacl)::kappa) sigma (RValue v))
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
.

