open String
open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let string_of_type ty = ASTio.(XAST.(to_string pprint_ml_type ty))

let rec iter_all_pairs f e = List.iter (fun e' -> f (e, e'))

let rec iter_all_pairs2 f = function
  | [] -> ()
  | hd::tl -> (iter_all_pairs f hd tl); (iter_all_pairs2 f tl)

let name_of_tname (TName x) = Name x
let name_of_lname (LName x) = Name x

let lname_of_tname (TName x) = LName x

let eq_tname (TName x) (TName y) = (x = y)

let upos = undefined_position

let rec program p = handle_error List.(fun () ->
  flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p))
)

and block env = function
  | BTypeDefinitions ts ->
    let env = type_definitions env ts in
    ([BTypeDefinitions ts], env)

  | BDefinition d ->
    let d, env = value_binding false env d in
    ([BDefinition d], env)

  | BClassDefinition c ->
    let ts, cmembers, env = class_definition env c in
    ((BTypeDefinitions ts) :: cmembers, env)

  | BInstanceDefinitions is ->
    let instances, env = instance_definition env is in
    ([instances], env)

(* Functions creating new symbols during elaboration. *)
and make_superdict_label (TName superclass_name) (TName class_name) =
  LName (lowercase (superclass_name ^ "_" ^ class_name))

and make_superdict_proj_name superclass_name class_name =
  name_of_lname (make_superdict_label superclass_name class_name)

and make_class_name class_name = lower_tname class_name

and make_dict_instance_name (TName class_name) (TName idx) =
  Name (lowercase (class_name ^ "_" ^ idx))

and make_dict_param_name class_name idx =
  let (Name instance_name) = make_dict_instance_name class_name idx in
  Name ("dict_" ^ instance_name)

and dict_param_name_from_pred (ClassPredicate(class_name, idx)) =
  make_dict_param_name class_name idx

and make_type_from_tname x =
  if is_ground_type x then
    TyApp(upos, x, [])
  else
    TyVar(upos, x)

and instantiate tparams =
  List.map (fun x -> make_type_from_tname x) tparams

(* Classes *)

(* TODO: check type of the class member (notably the use of unbound generic variable...) *)
and class_definition env cdef =
  check_wf_class env cdef;
  let env = bind_class cdef.class_name cdef env in
  let class_type, env = elaborate_class env cdef in
  let class_types = (TypeDefs (upos, [class_type])) in
  let env = type_definitions env class_types in
  let cmembers, env = elaborate_let_of_class_members env class_type in
  (class_types, cmembers, env)

(* Classes type checking. *)

and check_wf_class env cdef =
  check_superclasses env cdef

and check_superclasses env cdef =
  let check_is_superclass c1 c2 =
    if (is_superclass cdef.class_position c1 c2 env) then
      raise (SuperclassesCannotBeRelated(cdef.class_position, cdef.class_name, c1, c2)) in
  let check_both_superclass (c1, c2) =
    check_is_superclass c1 c2;
    check_is_superclass c2 c1 in
  iter_all_pairs2 check_both_superclass cdef.superclasses

(* Elaboration of classes. *)

and elaborate_class env cdef =
  let upos = undefined_position in
  let class_kind = KArrow(KStar, KStar) in
  let class_name = lower_tname cdef.class_name in
  let (superdicts, env) = elaborate_superdicts env cdef class_name in
  let class_dict = DRecordType ([cdef.class_parameter], superdicts @ cdef.class_members) in
  let elaborated_class_type = TypeDef (upos, class_kind, class_name, class_dict) in
  (elaborated_class_type, env)

and elaborate_superdicts env cdef class_name =
  let upos = undefined_position in
  let elaborate_superdict env superclass_name =
    let superdict_label = make_superdict_label superclass_name cdef.class_name in
    let superclass_name = lower_tname superclass_name in
    let field_type = 
      Types.(TyApp(upos, superclass_name, [TyVar (upos, cdef.class_parameter)])) in
    ((upos, superdict_label, field_type), env) in
  Misc.list_foldmap elaborate_superdict env cdef.superclasses

and elaborate_let_of_class_members env = function
  | TypeDef (_, _, dict_tname, dict_type) ->
    begin match dict_type with
    | DRecordType(tparams, members) ->
      let upos = undefined_position in
      let elaborate_let_of_class_member env (_, ((LName member_name) as lmember), member_type) =
        let local_dict_name = Name "dict" in
        let dict_lambda_type = TyApp(upos, dict_tname, instantiate tparams) in
        let dict_arg = (local_dict_name, dict_lambda_type) in
        let dict_lambda_body = ERecordAccess(upos, EVar(upos, local_dict_name, instantiate tparams), lmember) in
        let dict_lambda = ELambda(upos, dict_arg, dict_lambda_body) in
        let dict_access_binding = ((Name member_name), TyApp(upos, TName "->", [dict_lambda_type; member_type])) in
        let dict_access = ValueDef(upos, tparams, [], dict_access_binding, dict_lambda) in
        let env = bind_dict_access_value env upos tparams dict_access_binding in
        (BDefinition(BindValue(upos, [dict_access])), env) in
      Misc.list_foldmap elaborate_let_of_class_member env members
    | _ -> failwith "Elaboration of class members stored in a record only."
    end
  | _ -> failwith "Cannot elaborate external type."

and bind_dict_access_value env pos tparams (member_name, member_type) =
  begin try
    ignore (lookup pos member_name env);
    raise (CannotUseValueRestrictedName(pos, member_name))
  with
  | UnboundIdentifier _ ->
    bind_scheme member_name tparams member_type env
  end

(* Instance *)

and instance_definition env idefs = 
  let env = List.fold_left check_wf_instance env idefs in
  let instances, env = Misc.list_foldmap elaborate_instance env idefs in
  let e, env = value_binding true env (BindRecValue(upos, instances)) in
  (BDefinition(e), env)

(* Instance type checking *)

(* TODO: Check that all variables used in the typing context are also used in the "result type".
   Issue a warning if a variable is not used anywhere.
   Issue an error if a variable is only used in the typing context. *)
and check_wf_instance env idef =
  check_wf_typing_context_instance env idef;
  let env = bind_instance (ClassPredicate(idef.instance_class_name, idef.instance_index)) idef env in
  let cdef = lookup_class idef.instance_position idef.instance_class_name env in
  let tindex = lookup_type_definition idef.instance_position idef.instance_index env in
  (* TODO must be of kind  (KArrow(KStar, KStar)) *)
  ignore (type_definition env tindex);
  check_wf_instance_members env idef cdef;
  env

and check_wf_typing_context_instance env idef =
  let pos = idef.instance_position in
  let check_typing_context_relation () =
    let check_is_superclass c1 c2 =
      if (is_superclass pos c1 c2 env) then
        raise (InstanceTypingContextCannotBeRelated(pos, idef.instance_class_name, c1, c2)) in
    let check_is_identical c1 c2 =
      if (c1 = c2) then
        raise (InstanceTypingContextCannotBeEqual(pos, idef.instance_class_name, c1)) in
    let check_both_context (ClassPredicate(name1, idx1), ClassPredicate(name2, idx2)) =
      if (idx1 = idx2) then begin
        check_is_superclass name1 name2;
        check_is_superclass name2 name1;
        check_is_identical name1 name2
      end in
    iter_all_pairs2 check_both_context idef.instance_typing_context in

  let check_typing_context_existence () =
    let check_typing_context (ClassPredicate(name, idx)) =
      if List.mem idx idef.instance_parameters then
        ignore (lookup_class pos name env)
      else 
        Errors.fatal [start_of_position pos] 
          "Ground type are not allowed in the typing context." in 
    List.iter check_typing_context idef.instance_typing_context in

  check_typing_context_existence ();
  check_typing_context_relation ()

and check_wf_instance_members env idef cdef =
  let env = introduce_type_parameters env idef.instance_parameters in
  check_wf_instance_members_name env idef cdef

and check_wf_instance_members_name env idef cdef =
  let sort l = List.sort String.compare l in
  let inames = sort @@ List.map (fun (RecordBinding((LName mname), _)) -> mname) idef.instance_members in
  let cnames = sort @@ List.map (fun (_,(LName mname),_) -> mname) cdef.class_members in
  let rec check_members last il cl =
    match il, cl with
    | [], [] -> ()
    | ihd :: _, _ when last = ihd -> raise (AlreadyDefinedInstanceMember(idef.instance_position, LName(ihd)))
    | ihd :: _, [] -> raise (InstanceMemberNotInClass(idef.instance_position, cdef.class_name, LName(ihd)))
    | [], chd :: _ -> raise (MissingInstanceMember(idef.instance_position, cdef.class_name, LName(chd)))
    | ihd :: _, chd :: _ when ihd <> chd ->
        raise (InstanceMemberNotInClass(idef.instance_position, cdef.class_name, LName(chd)))
    | ihd :: itl, _ :: ctl -> check_members ihd itl ctl in
  check_members "" inames cnames

(* Instance elaboration *)

and elaborate_instance env idef =
  let class_name = make_class_name idef.instance_class_name in
  let instance_binding = make_instance_binding idef class_name in
  let super_dict_members = elaborate_instance_superdicts env idef class_name in
  let e = ERecordCon(upos, (name_of_tname class_name), 
    [TyApp(upos, idef.instance_index, instantiate idef.instance_parameters)], 
    super_dict_members @ idef.instance_members) in
  (ValueDef(upos, 
    idef.instance_parameters, 
    idef.instance_typing_context, 
    instance_binding, 
    EForall(upos, idef.instance_parameters, e)), env)

(* Name and type a dictionary instance function. *)
and make_instance_binding idef class_name =
  let instance_name = make_dict_instance_name idef.instance_class_name idef.instance_index in
  let result_type = make_instance_type idef.instance_parameters class_name idef.instance_index in
  (instance_name, result_type)

and make_instance_type tparams class_name idx =
  let idx_type = match tparams with
  | [] -> make_type_from_tname idx
  | p -> TyApp(upos, idx, instantiate p) in
  TyApp(upos, class_name, [idx_type]) 

and elaborate_instance_superdicts env idef class_name =
  let idx = idef.instance_index in
  let pos = idef.instance_position in
  let elaborate_superdict superdict_name =
    let superdict_builder_name = make_dict_instance_name superdict_name idx in
    let superdict_builder = EVar(upos, superdict_builder_name, (instantiate idef.instance_parameters)) in
    let superdict_label = make_superdict_label superdict_name class_name in
    RecordBinding(superdict_label, superdict_builder) in
  let superclasses = (lookup_class pos idef.instance_class_name env).superclasses in
  List.map elaborate_superdict superclasses


(* Term elaboration *)

and proj_dict_arg env (arg_name, arg_type) k idx =
  let (k', idx') = destruct_tydict_fatal upos arg_type in
  if not (eq_tname idx idx') then
    raise Not_found
  else
    let projection = EVar(upos, arg_name, []) in
    proj_dict env (projection, k') k (instantiate [idx])

and proj_dict env (dict_proj, dict_tproj) k instantiation =
  if eq_tname dict_tproj k then
    dict_proj
  else
    proj_superdicts env (dict_proj, dict_tproj) k instantiation

and proj_superdicts env (dict_proj, base_class) k instantiation =
  let rec aux = function
  | [] -> raise Not_found
  | superclass :: superclasses ->
    try
      let superclass = lower_tname superclass in
      let projector = 
        EVar(upos, make_superdict_proj_name superclass base_class, instantiation) in
      let projection = EApp(upos, projector, dict_proj) in
      proj_dict env (projection, superclass) k instantiation
    with
    | Not_found -> aux superclasses in
  aux (lookup_class upos base_class env).superclasses

and elaborate_variable_param pos env k idx =
  let rec find_matching_arg = function
  | [] -> raise (InaccessibleDictionaryInTypingContext(pos, k, idx))
  | dict :: dicts -> 
    try
      proj_dict_arg env dict k idx
    with
    | Not_found -> find_matching_arg dicts in
  find_matching_arg (dictionaries env)

and elaborate_dict_parameter env dict_tyname idx =
  let class_tname = make_class_name (lookup_class upos dict_tyname env).class_name in
  let elaborate_ground_param idx ts =
    let (_, (name, _)) = lookup_dict_instance env upos class_tname idx in
    let e, _ = elaborate_variable env upos name ts in
    e in
  match idx with
  | TyVar(_, idx) when is_ground_type idx ->
    elaborate_ground_param idx []
  | TyVar(pos, idx) ->
    elaborate_variable_param pos env class_tname idx
  | TyApp(_, idx, ts) ->
    elaborate_ground_param idx ts

and lookup_dict_instance env pos class_name idx =
  let instance_name = make_dict_instance_name class_name idx in
  try
    lookup pos instance_name env
  with
  | UnboundIdentifier _ -> raise (UndeclaredInstance(pos, class_name, idx))

and elaborate_parameters env expr = function
  | [] -> expr
  | TyApp(_, dict_tyname, [idx]) :: tys ->
    begin try
      let dict_param = elaborate_dict_parameter env dict_tyname idx in
      let dict_app = EApp(upos, expr, dict_param) in
      elaborate_parameters env dict_app tys
    with UnboundClass _ -> expr
    end
  | _ -> expr

and elaborate_variable env pos name tys =
  let ty = type_application pos env name tys in
  let param_tys, _ = destruct_ntyarrow ty in
  let var = EVar(pos, name, tys) in
  let e = elaborate_parameters env var param_tys in
  (e, elaborated env)

(* Function introducing the dictionaries as lambda when a dictionary is available. *)

and introduce_typing_context env ps =
  let introduce_dict env param =
    bind_dict param env in
  let params = dict_params ps in
  List.fold_left introduce_dict env params

(* Precondition: 'e' do not contain type abstractions. *)
and introduce_dictionaries ts ps e ty =
 let (e, ty) = introduce_dictionaries_lambda ps e ty in
 (EForall(upos, ts, e), ty)

(* Precondition: 'e' do not contain type abstractions. *)
and introduce_dictionaries_lambda ps e ty =
  let introduce_lambda e param = 
    ELambda(upos, param, e) in
  let introduce_lambda_type ty (_, arg_type) =
    ntyarrow upos [arg_type] ty in
  let params = dict_params ps in
  let e = List.fold_left introduce_lambda e params in
  let ty = List.fold_left introduce_lambda_type ty params in
  (e, ty)

and dict_params ps =
  let dict_param class_pred =
    let dict_name = dict_param_name_from_pred class_pred in
    let dict_type = dict_type_from_pred class_pred in
    (dict_name, dict_type) in
  List.map dict_param ps

and dict_type_from_pred (ClassPredicate(class_name, idx)) = 
  make_instance_type [] (make_class_name class_name) idx

and type_definitions env (TypeDefs (_, tdefs)) =
  let env = List.fold_left env_of_type_definition env tdefs in
  List.fold_left type_definition env tdefs

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    bind_type t kind tdef env
  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition env = function
  | TypeDef (pos, _, t, dt) -> datatype_definition t env dt
  | ExternalType (p, ts, t, os) -> env

and datatype_definition t env = function
  | DAlgebraic ds ->
    List.fold_left algebraic_dataconstructor env ds
  | DRecordType (ts, ltys) ->
    List.fold_left (label_type ts t) env ltys

and label_type ts rtcon env (pos, l, ty) =
  let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
  check_wf_type env' KStar ty;
  bind_label pos l ts ty rtcon env

and algebraic_dataconstructor env (_, DName k, ts, kty) =
  check_wf_scheme env ts kty;
  bind_scheme (Name k) ts kty env

and introduce_type_parameters env ts =
  List.fold_left (fun env t -> bind_type_variable t env) env ts

and check_wf_scheme env ts ty =
  check_wf_type (introduce_type_parameters env ts) KStar ty

and check_wf_type env xkind = function
  | TyVar (pos, t) ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind

  | TyApp (pos, t, tys) ->
    let kt = lookup_type_kind pos t env in
    check_type_constructor_application pos env kt tys

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> ()
  | ty :: tys, KArrow (k, ks) ->
    check_wf_type env k ty;
    check_type_constructor_application pos env ks tys
  | _ ->
    raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
    | KStar, KStar -> ()
    | KArrow (k1, k2), KArrow (k1', k2') ->
      check_equivalent_kind pos k1 k1';
      check_equivalent_kind pos k2 k2'
    | _ ->
      raise (IncompatibleKinds (pos, k1, k2))

and env_of_bindings env cdefs = List.(
  (function
    | BindValue (_, vs)
    | BindRecValue (_, vs) ->
      fold_left (fun env (ValueDef (_, ts, _, (x, ty), _)) ->
        bind_scheme x ts ty env
      ) env vs
    | ExternalValue (_, ts, (x, ty), _) ->
      bind_scheme x ts ty env
  ) cdefs
)

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2) then
    raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  List.iter (check_wf_type env KStar) tys;
  let (ts, (_, ty)) = lookup pos x env in
  try
    substitute (List.combine ts tys) ty
  with _ ->
    raise (InvalidTypeApplication pos)

and expression env = function
  | EVar (pos, ((Name s) as x), tys) ->
    if (is_elaborated env) then
      (EVar (pos, x, tys), type_application pos env x tys)
    else
      let e, env = elaborate_variable env pos x tys in
      expression env e

  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple x aty env in
    let (e, ty) = expression env e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)

  | EApp (pos, a, b) ->
    let a, a_ty = expression env a in
    let b, b_ty = expression env b in
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end

  | EBinding (pos, vb, e) ->
    let vb, env = value_binding false env vb in
    let e, ty = expression env e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables
        are useless. *)
    expression env e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
          let (e, ty) = expression env e in
          check_equal_types pos ty xty;
          e
        ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression env s in
    let bstys = List.map (branch env sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env e in
    let (ts, lty, rtcon) = lookup_label pos l env in
    let ty =
      match ty with
        | TyApp (_, r, args) ->
          if rtcon <> r then
            raise (LabelDoesNotBelong (pos, l, r, rtcon))
          else
            begin try
              let s = List.combine ts args in
              Types.substitute s lty
            with _ ->
              (** Because we only well-kinded types and only store
                  well-kinded types in the environment. *)
              assert false
            end
        | _ ->
          raise (RecordExpected (pos, ty))
    in
    (ERecordAccess (pos, e, l), ty)

  | ERecordCon (pos, n, i, []) ->
    (** We syntactically forbids empty records. *)
    assert false

  | ERecordCon (pos, n, i, rbs) ->
    let rbstys = List.map (record_binding env) rbs in
    let rec check others rty = function
      | [] ->
        begin match rty with
          | Some (_, TyApp (_, rtcon, _)) ->
            let labels = labels_of rtcon env in
            if (List.length labels <> List.length others) then
              raise (InvalidRecordConstruction pos)
          | _ -> assert false (** Because we forbid empty record. *)
        end;
        List.rev others, rty
      | (RecordBinding (l, e), ty) :: ls ->
        if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
          raise (MultipleLabels (pos, l));

        let (ts, lty, rtcon) = lookup_label pos l env in
        let (s, rty) =
          match rty with
            | None ->
              let rty = TyApp (pos, rtcon, i) in
              let s =
                try
                  List.combine ts i
                with _ -> raise (InvalidRecordInstantiation pos)
              in
              (s, rty)
            | Some (s, rty) ->
              (s, rty)
        in
        check_equal_types pos ty (Types.substitute s lty);
        check (RecordBinding (l, e) :: others) (Some (s, rty)) ls
    in
    let (ls, rty) = check [] None rbstys in
    let rty = match rty with
      | None -> assert false
      | Some (_, rty) -> rty
    in
    (ERecordCon (pos, n, i, ls), rty)

  | ((EPrimitive (pos, p)) as e) ->
    (e, primitive pos p)

and primitive pos = function
  | PIntegerConstant _ ->
    TyApp (pos, TName "int", [])

  | PUnit ->
    TyApp (pos, TName "unit", [])

  | PCharConstant _ ->
    TyApp (pos, TName "char", [])

and branch env sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression env e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, (x, ty)) -> bind_simple x ty env)
    env1 (values env2)

and linear_bind pos env (ts, (x, ty)) =
  assert (ts = []); (** Because patterns only bind monomorphic values. *)
  try
    ignore (lookup pos x env);
    raise (NonLinearPattern pos)
  with UnboundIdentifier _ ->
    bind_simple x ty env

and join pos denv1 denv2 =
  List.fold_left (linear_bind pos) denv2 (values denv1)

and check_same_denv pos denv1 denv2 =
  List.iter (fun (ts, (x, ty)) ->
    assert (ts = []); (** Because patterns only bind monomorphic values. *)
    try
      let (_, (_, ty')) = lookup pos x denv2 in
      check_equal_types pos ty ty'
    with _ ->
      raise (PatternsMustBindSameVariables pos)
  ) (values denv1)

and pattern env xty = function
  | PVar (_, name) ->
    bind_simple name xty ElaborationEnvironment.empty

  | PWildcard _ ->
    ElaborationEnvironment.empty

  | PAlias (pos, name, p) ->
    linear_bind pos (pattern env xty p) ([], (name, xty))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, p) ->
    check_equal_types pos (primitive pos p) xty;
    ElaborationEnvironment.empty

  | PData (pos, (DName x), tys, ps) ->
    let kty = type_application pos env (Name x) tys in
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos)
    else
      let denvs = List.map2 (pattern env) itys ps in (
        check_equal_types pos oty xty;
        List.fold_left (join pos) ElaborationEnvironment.empty denvs
      )

  | PAnd (pos, ps) ->
    List.fold_left
      (join pos)
      ElaborationEnvironment.empty
      (List.map (pattern env xty) ps)

  | POr (pos, ps) ->
    let denvs = List.map (pattern env xty) ps in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    denv

and record_binding env (RecordBinding (l, e)) =
  let e, ty = expression env e in
  (RecordBinding (l, e), ty)

and value_binding force_elaboration env = function
  | BindValue (pos, vs) ->
    let vs = List.map (value_elaboration force_elaboration env) vs in
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let vs = List.map (value_elaboration force_elaboration env) vs in
    let env = List.fold_left value_declaration env vs in
    let (vs, _) = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, ((x, ty) as b), os) ->
    let env = bind_scheme x ts ty env in
    (ExternalValue (pos, ts, b, os), env)

and eforall pos ts e =
  match ts, e with
  | ts, EForall (pos, [], ((EForall _) as e)) ->
    eforall pos ts e
  | [], EForall (pos, [], e) ->
    e
  | [], EForall (pos, _, _) ->
    raise (InvalidNumberOfTypeAbstraction pos)
  | [], e ->
    e
  | x :: xs, EForall (pos, t :: ts, e) ->
    if x <> t then
      raise (SameNameInTypeAbstractionAndScheme pos);
    eforall pos xs (EForall (pos, ts, e))
  | _, _ ->
    raise (InvalidNumberOfTypeAbstraction pos)

and value_definition env (ValueDef (pos, ts, ps, (x, xty), e)) =
  let env' = introduce_type_parameters env ts in
  let env' = introduce_typing_context env' ps in
  let e = eforall pos ts e in
  let e, ty = expression env' e in
  let b = (x, ty) in
  check_equal_types pos xty ty;
  (ValueDef (pos, ts, [], b, EForall (pos, ts, e)), 
   bind_scheme x ts ty env)

and value_elaboration force_elaboration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  let env' = introduce_type_parameters env ts in
  check_wf_scheme env' ts ty;

  if not force_elaboration && not (is_function ty) && ps <> [] then
    raise (ClassPredicateInValueForbidden(pos,x))
  else if not (is_value_form e) && ts <> [] then
    raise (ValueRestriction pos)
  else if ps <> [] then
    let e = eforall pos ts e in
    let e, ty = introduce_dictionaries ts ps e ty in
    ValueDef(pos, ts, ps, (x, ty), e)
  else
    ValueDef(pos, ts, ps, (x, ty), e)

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  bind_scheme x ts ty env

and is_function ty =
  match destruct_tyarrow ty with
  | Some _ -> true
  | None -> false

and is_value_form = function
  | EVar _
  | ELambda _
  | EPrimitive _ ->
    true
  | EDCon (_, _, _, es) ->
    List.for_all is_value_form es
  | ERecordCon (_, _, _, rbs) ->
    List.for_all (fun (RecordBinding (_, e)) -> is_value_form e) rbs
  | EExists (_, _, t)
  | ETypeConstraint (_, t, _)
  | EForall (_, _, t) ->
    is_value_form t
  | _ ->
    false

