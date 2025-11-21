# Preprocessing class: FSLSSMSMSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting C07_19_nc_SOS_SAT001_MinMin_p005000_rr with 5s (1) cores
# C07_19_nc_SOS_SAT001_MinMin_p005000_rr with pid 13516 completed with status 0
# Result found by C07_19_nc_SOS_SAT001_MinMin_p005000_rr
# Preprocessing class: FSLSSMSMSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting C07_19_nc_SOS_SAT001_MinMin_p005000_rr with 5s (1) cores
# No SInE strategy applied
# Search class: FGHSM-FSLM32-MFFFFFBN
# partial match(1): FGHSM-FSLM32-MFFFFFNN
# Scheduled 5 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_303_C18_F1_URBAN_S0Y with 1s (1) cores
# G-E--_303_C18_F1_URBAN_S0Y with pid 13521 completed with status 0
# Result found by G-E--_303_C18_F1_URBAN_S0Y
# Preprocessing class: FSLSSMSMSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting C07_19_nc_SOS_SAT001_MinMin_p005000_rr with 5s (1) cores
# No SInE strategy applied
# Search class: FGHSM-FSLM32-MFFFFFBN
# partial match(1): FGHSM-FSLM32-MFFFFFNN
# Scheduled 5 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_303_C18_F1_URBAN_S0Y with 1s (1) cores

# Proof found!
# SZS status Theorem
# SZS output start CNFRefutation
tff(decl_sort1, type, a: $tType).
tff(decl_80, type, p: a > $o).
tff(decl_109, type, esk23_0: a).
tff(conj_0, conjecture, ![X144:a]:((~(p(X144))|p(X144))), file('/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4976412_1.p', conj_0)).
tff(c_0_1, negated_conjecture, ~(![X144:a]:((~p(X144)|p(X144)))), inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])])).
tff(c_0_2, negated_conjecture, (p(esk23_0)&~p(esk23_0)), inference(fof_nnf,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])])).
tcf(c_0_3, negated_conjecture, p(esk23_0), inference(split_conjunct,[status(thm)],[c_0_2])).
tcf(c_0_4, negated_conjecture, ~p(esk23_0), inference(split_conjunct,[status(thm)],[c_0_2])).
cnf(c_0_5, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_3, c_0_4]), ['proof']).
# SZS output end CNFRefutation