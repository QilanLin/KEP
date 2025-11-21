% WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
% WARNING: option i not known.
% dis+1002_1:1_bd=off:fd=off:sos=on:i=601:si=on:rtra=on_0 on prob4765072_min_1 for (3ds)
% Refutation found. Thanks to Tanya!
% SZS status Theorem for prob4765072_min_1
% SZS output start Proof for prob4765072_min_1
tff(type_def_5, type, a: $tType).
tff(func_def_0, type, sK0: a).
tff(pred_def_1, type, p: (a) > $o).
tff(f8,plain,(
  $false),
  inference(subsumption_resolution,[],[f7,f6])).
tff(f6,plain,(
  ~p(sK0)),
  inference(cnf_transformation,[],[f5])).
tff(f5,plain,(
  p(sK0) & ~p(sK0)),
  inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f4])).
tff(f4,plain,(
  ? [X0 : a] : (p(X0) & ~p(X0)) => (p(sK0) & ~p(sK0))),
  introduced(choice_axiom,[])).
tff(f3,plain,(
  ? [X0 : a] : (p(X0) & ~p(X0))),
  inference(ennf_transformation,[],[f2])).
tff(f2,negated_conjecture,(
  ~! [X0 : a] : (p(X0) | ~p(X0))),
  inference(negated_conjecture,[],[f1])).
tff(f1,conjecture,(
  ! [X0 : a] : (p(X0) | ~p(X0))),
  file('/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4765072_min_1.p',conj_0)).
tff(f7,plain,(
  p(sK0)),
  inference(cnf_transformation,[],[f5])).
% SZS output end Proof for prob4765072_min_1
% ------------------------------
% Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
% Termination reason: Refutation

% Memory used [KB]: 895
% Time elapsed: 0.002 s
% ------------------------------
% ------------------------------
% Success in time 0.008 s